# Code and documentation fixes (not errata)

The repository has no tagged release and the paper links only the repository, so these are not errata. All land
before the Palomar commit (R21); each is a minimal diff with a test. Seeds from planning; "confirm" means read the
code once more before editing.

| ID | File | Fix (minimal) | Test | Status |
|---|---|---|---|---|
| L01 | `native/selfmodgraph.cpp` `tarjan_scc` | outer loop must skip nodes already visited (today a visited SCC root is re-emitted as a duplicate singleton and a visited non-root is left on the stack); `twosat` is unaffected | duplicate-free SCC list; `twosat` vectors unchanged | open |
| L02 | `native/aesmain.c`, `native/rsa.c` | label the VM slot honestly ("Graph VM", not "Irreducible Loop Graph Encryption"); drop or guard the empty AES-192/256 stubs and the commented-out `AES_128_obf_il_encrypt` | harness output | open |
| L03 | `python/virt.py` `set_bit_range` | slice stop, not stride (`num[a::b]`); only if used, else delete (confirm) | unit test | open |
| L04 | `python/virt.py` `do_run_virtual` | define `outp = None` when `outmap is None` (NameError today; confirm) | unit test | open |
| L05 | `python/virt.py`, `aes.py`, `rsa.py` | optional `--seed` for reproducible graph regeneration (`subg_virtual` and `multi_bit_selection_to_table_virtual` call an unseeded `random.shuffle`); default behaviour unchanged | `graph_stats.py` twice gives identical counts | open |
| L06 | `python/aes.py` `gen_aes` | document that the key is `0x12...` per byte (the paper says "fixed randomly generated key", see P11); key choice per the author's answer | regenerate | open |
| L07 | `native/*.vcxproj`, `generated/` | native `aes` and `ecdsa` projects need more than the 1.5 GB local compile cap for the 10.8 MB `generated/aesvm.cpp` and for `ecdsa256vm.c` (C1060 out of heap space); document CI-only or split the generated sources (R0 finding) | CI compile | open |
| D01 | `README.md` | Lean section (R24); Palomar ID and tag after registration (R25) | | open |
| D02 | `CITATION.cff` | add the formalization reference after registration | | open |
| D03 | `README.md` / `CHANGELOG.md` | state that the irreducible-loop-protected AES/RSA variant and the planted 2-SAT generator of Section 3.1 are not implemented in the repository (per the P13 answer) | | open |
