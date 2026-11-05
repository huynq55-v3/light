# File: run_gemma_os.py
import subprocess, torch
from transformers import AutoTokenizer, AutoModelForCausalLM
import unicodedata

MODEL_DIR = "./gemma_local_model"
print(f"🚀 [1/2] Đang nạp trực tiếp HuggingFace repo '{MODEL_DIR}' trên CPU...")

tokenizer = AutoTokenizer.from_pretrained(MODEL_DIR)
model = AutoModelForCausalLM.from_pretrained(
    MODEL_DIR,
    dtype=torch.bfloat16,
    device_map="cpu",
    low_cpu_mem_usage=True,
)
print("✅ Mô hình Gemma đã sẵn sàng! Đang khởi động Light OS...")

# Khởi chạy QEMU (Không cần weights.bin nữa!)
qemu = subprocess.Popen(
    [
        "qemu-system-x86_64", "-enable-kvm", "-cpu", "host", "-m", "8G",
        "-kernel", "kernel.elf",
        "-drive", "file=disk.img,format=raw",
        "-serial", "stdio",
    ],
    stdin=subprocess.PIPE,
    stdout=subprocess.PIPE,
    bufsize=0,
)

buf = bytearray()
while qemu.poll() is None:
    ch = qemu.stdout.read(1)
    if not ch:
        break
    if ch == b"\x04":
        text = buf.decode("ascii", errors="ignore")
        buf.clear()
        user_msg = text.strip().split(">")[-1].strip()
        if not user_msg:
            qemu.stdin.write(b"PLEASE TYPE A MESSAGE.\x04")
            qemu.stdin.flush()
            continue

        print(f"\n📩 [Light OS Prompt]: {user_msg}")

        # Dùng chuẩn Chat Template của Gemma để model trả lời thông minh, không bị lặp từ!
        messages = [
            {"role": "user", "content": f"Reply in 1 short sentence (plain ASCII): {user_msg}"}
        ]
        prompt = tokenizer.apply_chat_template(messages, tokenize=False, add_generation_prompt=True)
        inputs = tokenizer(prompt, return_tensors="pt").to("cpu")

        with torch.no_grad():
            out = model.generate(
                **inputs,
                max_new_tokens=25,
                do_sample=False,
                pad_token_id=tokenizer.eos_token_id,
            )

        reply = tokenizer.decode(out[0][inputs.input_ids.shape[1]:], skip_special_tokens=True)
        no_accent = unicodedata.normalize("NFKD", reply.replace("đ", "d").replace("Đ", "D"))
        clean_reply = "".join(c for c in no_accent.upper().replace("\n", " ") if 32 <= ord(c) < 127).strip()[:120]
        print(f"🤖 [Gemma Reply]: {clean_reply}")

        qemu.stdin.write(clean_reply.encode("ascii") + b"\x04")
        qemu.stdin.flush()
    else:
        buf.extend(ch)
