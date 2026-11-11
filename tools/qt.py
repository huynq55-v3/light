# tools/qt.py <tiền_tố_ra> <chế độ legacy|uefi|usb|usb2> <lệnh...>: chạy QEMU không màn hình, điều khiển qua QMP
# Lệnh: wait:S  key:QCODE  type:TEXT (dùng $'..\n' để gõ Enter)  shot:TÊN  mouse:DX,DY  click  down  up (giữ/nhả nút trái, để kéo)  mon:LỆNH_MONITOR (vd 'xp /4gx 0x79800')  quit
# Thư mục ra (serial, ảnh, ảnh đĩa tạm): $QT_OUT (mặc định /tmp/lightqt). RAM: $QT_MEM (mặc định 4G). Chuột PS/2/USB tương đối: 1 đơn vị = 2 pixel.
# usb = 1 xHCI (bàn phím + chuột); usb2 = 2 xHCI (chuột ở controller 1, bàn phím ở controller 2);
# usbx = 1 xHCI + thiết bị theo $QT_DEV (vd 'usb-hub,bus=xhci.0,port=1 usb-kbd,bus=xhci.0,port=1.1'), máy theo $QT_MACHINE.
import json, socket, subprocess, sys, time, os
R = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
S = os.environ.get('QT_OUT', '/tmp/lightqt'); os.makedirs(S, exist_ok=True)
out, mode, cmds = sys.argv[1], sys.argv[2], sys.argv[3:]
q = f'{S}/qmp.sock'
if os.path.exists(q): os.remove(q)
base = ['qemu-system-x86_64', '-enable-kvm', '-cpu', 'host', '-m', os.environ.get('QT_MEM', '4G'), '-smp', '8', '-display', 'none', '-qmp', f'unix:{q},server,nowait', '-serial', f'file:{S}/{out}_serial.txt']
if mode in ('legacy', 'usb', 'usb2', 'usbx'):
    subprocess.run(['cp', f'{R}/disk.img', f'{S}/disk64.img']); subprocess.run(['truncate', '-s', '64M', f'{S}/disk64.img'])
    base += ['-kernel', f'{R}/kernel.elf', '-drive', f'file={S}/disk64.img,format=raw,if=ide']
    if mode == 'usb':
        base += ['-machine', 'pc,i8042=off,vmport=off', '-device', 'qemu-xhci,id=xhci', '-device', 'usb-kbd,bus=xhci.0', '-device', 'usb-mouse,bus=xhci.0']
    if mode == 'usbx':
        # thiết bị USB tùy chọn: $QT_MACHINE (mặc định pc,i8042=off,vmport=off), $QT_DEV = các tham số -device cách nhau bởi dấu cách
        base += ['-machine', os.environ.get('QT_MACHINE', 'pc,i8042=off,vmport=off'), '-device', 'qemu-xhci,id=xhci']
        for d in os.environ.get('QT_DEV', '').split():
            base += ['-device', d]
    if mode == 'usb2':
        base += ['-machine', 'pc,i8042=off,vmport=off', '-device', 'qemu-xhci,id=xhci', '-device', 'usb-mouse,bus=xhci.0', '-device', 'qemu-xhci,id=xhci2', '-device', 'usb-kbd,bus=xhci2.0']
else:
    W = f'{S}/uefi'; os.makedirs(W, exist_ok=True)
    p = subprocess.Popen(['bash', f'{R}/tools/qemu_uefi_nvme.sh', W, '-display', 'none', '-qmp', f'unix:{q},server,nowait'], stdout=open(f'{S}/{out}_serial.txt', 'w'), stderr=subprocess.STDOUT)
if mode != 'uefi':
    p = subprocess.Popen(base, stdout=subprocess.DEVNULL, stderr=subprocess.STDOUT)
for _ in range(100):
    if os.path.exists(q): break
    time.sleep(0.1)
time.sleep(0.3)
s = socket.socket(socket.AF_UNIX); s.connect(q); f = s.makefile('rw')
def cmd(c, **a):
    f.write(json.dumps({'execute': c, 'arguments': a}) + '\n'); f.flush()
    while True:
        r = json.loads(f.readline())
        if 'return' in r or 'error' in r: return r
f.readline(); cmd('qmp_capabilities')
def key(k, down):
    cmd('input-send-event', events=[{'type': 'key', 'data': {'down': down, 'key': {'type': 'qcode', 'data': k}}}])
def tap(k, shift=False):
    if shift: key('shift', True)
    key(k, True); time.sleep(0.05); key(k, False)
    if shift: key('shift', False)
    time.sleep(0.08)
for c in cmds:
    op, _, arg = c.partition(':')
    if op == 'wait': time.sleep(float(arg))
    elif op == 'key': tap(arg)
    elif op == 'type':
        for ch in arg:
            if ch == ' ': tap('spc')
            elif ch == '\n': tap('ret')
            elif ch.isupper(): tap(ch.lower(), True)
            else: tap({'.': 'dot', '-': 'minus', '/': 'slash'}.get(ch, ch))
    elif op == 'shot':
        cmd('screendump', filename=f'{S}/{arg}.ppm')
        subprocess.run([sys.executable, '-c', f"from PIL import Image; Image.open('{S}/{arg}.ppm').save('{S}/{arg}.png')"])
    elif op == 'mouse':
        dx, dy = map(int, arg.split(','))
        cmd('input-send-event', events=[{'type': 'rel', 'data': {'axis': 'x', 'value': dx}}, {'type': 'rel', 'data': {'axis': 'y', 'value': dy}}])
        time.sleep(0.1)
    elif op == 'mon':
        print(arg, '=>', cmd('human-monitor-command', **{'command-line': arg}).get('return', '').strip())
    elif op in ('down', 'up'):
        cmd('input-send-event', events=[{'type': 'btn', 'data': {'down': op == 'down', 'button': 'left'}}]); time.sleep(0.2)
    elif op == 'click':
        cmd('input-send-event', events=[{'type': 'btn', 'data': {'down': True, 'button': 'left'}}]); time.sleep(0.1)
        cmd('input-send-event', events=[{'type': 'btn', 'data': {'down': False, 'button': 'left'}}]); time.sleep(0.2)
cmd('quit')
p.wait(timeout=10)
