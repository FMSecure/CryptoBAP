from __future__ import annotations


CASE_TEMPLATES: dict[str, str] = {
    "xor": """name: xor
description: Checked-in XOR running example.
arch: arm8
channel: Channel
input:
  # binary: path/to/raw-binary.elf
  da: examples/binaries/protocols/xor/xor.da
  disassembly:
    tool: ghidra
    sections: [.text]
  theory: XORexample
  symbols: [new_key, senc, send, main]
execution:
  entry_label: 60
  exit_labels: [132]
  extra_variables:
    - name: key
      type: Imm
      width: 64
functions:
  library: [senc, new_key, send]
  adversary: [recv]
  crypto:
    send: MEMcpy
    new_key: OTP
    senc: XOR
artifacts:
  sapic_source: examples/protocols/xor/Sapic_Translation.txt
  tamarin_source: examples/backend-results/xor.spthy
backends: [tamarin, squirrel]
proof_status:
  hol: generated_unchecked
  sapic: generated_unchecked
  squirrel: generated_unchecked
security_lemmas: []
""",
    "tinyssh": """name: tinyssh
description: Checked-in TinySSH server example.
arch: arm8
channel: Channel
input:
  # binary: path/to/raw-binary.elf
  da: examples/binaries/protocols/tinyssh/tinysshd.da
  disassembly:
    tool: ghidra
    sections: [.text]
  theory: TinySSHexample
  symbols: [main, tinyssh_dec, tinyssh_enc, tinyssh_hash, AcceptS, AcceptS2, receive_new_key, kdfPtoS, kdfStoP]
execution:
  fragments:
    - name: accept_server
      entry_label: 0x403D20
      exit_labels: [0x404794]
    - name: receive_new_key
      entry_label: 0x402730
      exit_labels: [0x403160]
  extra_variables:
    - name: key
      type: Imm
      width: 64
functions:
  library: [kdfPtoS]
  adversary: [packet_getall]
  crypto:
    kdfPtoS: KDF
    tinyssh_enc: ENC
    tinyssh_dec: DEC
artifacts:
  sapic_source: examples/protocols/tinyssh/Sapic_Translation.txt
  tamarin_source: examples/backend-results/tinyssh.spthy
backends: [tamarin, squirrel]
proof_status:
  hol: generated_unchecked
  tamarin: generated_unchecked
  squirrel: generated_unchecked
security_lemmas: [sanity_AcceptP, sanity_AcceptS, injPS, injSP, key_secrecy]
""",
    "wireguard-init": """name: wireguard-init
description: Checked-in WireGuard initiator example.
arch: arm8
channel: Channel
input:
  # binary: path/to/raw-binary.elf
  da: examples/binaries/protocols/wireguard/wireguard.da
  disassembly:
    tool: ghidra
    sections: [.text]
  theory: Winitexample
  symbols: [handshake_init, message_encrypt, message_ephemeral, mix_dh, mix_precomputed_dh, mix_psk]
execution:
  fragments:
    - name: init_1
      entry_label: 3048
      exit_labels: [3264, 3464]
    - name: init_2
      entry_label: 4640
      exit_labels: [5312, 5252]
  extra_variables:
    - name: key
      type: Imm
      width: 64
functions:
  library: [message_encrypt, message_decrypt]
  adversary: [down_read]
  crypto:
    message_encrypt: AEAD_ENC
    message_decrypt: AEAD_DEC
    mix_dh: DH
    mix_psk: KDF
artifacts:
  sapic_source: examples/protocols/wireguard-init/Sapic_Translation.txt
  tamarin_source: examples/backend-results/wireguard.spthy
backends: [tamarin, squirrel]
proof_status:
  hol: generated_unchecked
  tamarin: generated_unchecked
  squirrel: generated_unchecked
security_lemmas: [injIP, injPI, key_secrecy]
""",
    "wireguard-resp": """name: wireguard-resp
description: Checked-in WireGuard responder example.
arch: arm8
channel: Channel
input:
  # binary: path/to/raw-binary.elf
  da: examples/binaries/protocols/wireguard/wireguard.da
  disassembly:
    tool: ghidra
    sections: [.text]
  theory: Wrespexample
  symbols: [message_decrypt, message_encrypt, message_ephemeral, mix_dh, mix_precomputed_dh, mix_psk]
execution:
  fragments:
    - name: response_1
      entry_label: 3544
      exit_labels: [3768, 4180, 4204]
    - name: response_2
      entry_label: 4384
      exit_labels: [4620, 4380]
  extra_variables:
    - name: key
      type: Imm
      width: 64
functions:
  library: [message_encrypt, message_decrypt]
  adversary: [down_read]
  crypto:
    message_encrypt: AEAD_ENC
    message_decrypt: AEAD_DEC
    mix_dh: DH
    mix_psk: KDF
artifacts:
  sapic_source: examples/protocols/wireguard-resp/Sapic_Translation.txt
  tamarin_source: examples/backend-results/wireguard.spthy
backends: [tamarin, squirrel]
proof_status:
  hol: generated_unchecked
  tamarin: generated_unchecked
  squirrel: generated_unchecked
security_lemmas: [injIP, injPI, key_secrecy]
""",
}
