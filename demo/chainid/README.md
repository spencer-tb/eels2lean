# chain_id demo: ethereum/execution-specs#3828

eels2lean on a real EELS bug: legacy `chain_id` raised `OverflowError` for `v >= 2**65 + 35` from ethereum/execution-specs#3000 until ethereum/execution-specs#3828.

`chain_id` in `ethereum.forks.amsterdam.transactions` is translated from EELS as it is, with its `Transaction` union, `isinstance` and `None | U64` result. Nothing here is hand-written except the proofs.

- `ChainIdPre`: the translation at `16898000911`, the commit eels2lean pins, which still has the bug.
- `ChainIdPost`: the translation at `067505d633`, the fix.
- `lean/ChainIdProofs`:
  - `Post.only_raises_bad_v`, the allowlist: the only exception `chain_id` raises, for any transaction, is the one its own `raise` statements name, `InvalidSignatureError`. `Post.never_overflows` follows as a corollary.
  - `Pre.overflows_at` and `Pre.overflows_iff`: on the pre-fix code, a legacy transaction raises `OverflowError` exactly when `v >= 2**65 + 35`.
  - `PreAttempt.lean`: the same proofs as `Post`, which fail on the pre-fix code with `h : Exc.OverflowError = e ⊢ False`.
  - `EvalPre.lean`, `EvalPost.lean`: the generated `chain_id` run at the 64-bit boundary.
- `eels_ground_truth.py`: the EELS Python `chain_id` at the same inputs, for comparison.

```sh
just snapshot   # the pinned commit; 067505d633 goes into .cache/eels/ the same way
pre=16898000911c1e3caa57be08509536c10ae92d3e
post=067505d633f708809f03dda92034592395dd715e
uv run python -m eels2lean --src .cache/eels/$pre/src --out lean --pin $pre --root ChainIdPre ethereum.forks.amsterdam.transactions.chain_id
uv run python -m eels2lean --src .cache/eels/$post/src --out lean --pin $post --root ChainIdPost ethereum.forks.amsterdam.transactions.chain_id
cd lean
lake build ChainIdProofs.Pre ChainIdProofs.Post ChainIdProofs.EvalPre ChainIdProofs.EvalPost
lake env lean ChainIdProofs/PreAttempt.lean   # expected to fail
cd ..
$EELS/.venv/bin/python -I demo/chainid/eels_ground_truth.py .cache/eels/$pre/src
$EELS/.venv/bin/python -I demo/chainid/eels_ground_truth.py .cache/eels/$post/src
```
