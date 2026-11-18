"""
Call the real EELS `chain_id` on legacy transactions around the 64-bit
boundary, at one EELS snapshot. Run with the EELS virtual environment:

    .venv/bin/python -I eels_ground_truth.py SNAPSHOT/src
"""

import sys

sys.path.insert(0, sys.argv[1])

from ethereum_types.bytes import Bytes, Bytes0  # noqa: E402
from ethereum_types.numeric import U256, Uint  # noqa: E402

from ethereum.forks.amsterdam.transactions import (  # noqa: E402
    LegacyTransaction,
    chain_id,
)

for label, v in [
    ("2**65 + 34 (largest chain id 2**64 - 1)", 2**65 + 34),
    ("2**65 + 35 (chain id 2**64)", 2**65 + 35),
    ("2**256 - 1", 2**256 - 1),
]:
    tx = LegacyTransaction(
        nonce=U256(0), gas_price=Uint(0), gas=Uint(0), to=Bytes0(),
        value=U256(0), data=Bytes(), v=U256(v), r=U256(1), s=U256(1),
    )
    try:
        print(f"v = {label}: ok {chain_id(tx)}")
    except Exception as error:  # noqa: BLE001
        print(f"v = {label}: {type(error).__name__}: {error}")
