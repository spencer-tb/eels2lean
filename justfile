pin := `grep '^commit' eels.toml | cut -d'"' -f2`
eels := env("EELS", home_directory() / "ethereum/execution-specs")
src := ".cache/eels" / pin / "src"
cases := "tests/cases"
gas := "ethereum.forks.amsterdam.vm.gas."
pure := gas + "max_message_call_gas " + gas + "calculate_memory_gas_cost " + gas + "init_code_cost ethereum.utils.numeric.ceil32 " + gas + "calculate_message_call_gas " + gas + "allocate_evm_gas"
meter := gas + "charge_gas_from_meter " + gas + "charge_state_gas_from_meter " + gas + "commit_state_gas " + gas + "restore_state_gas " + gas + "restore_state_gas_to_entry " + gas + "tx_state_gas_used " + gas + "credit_state_gas_refund " + gas + "repay_state_gas_spill " + gas + "forfeit_remaining_gas " + gas + "withhold_create_gas " + gas + "drain_state_gas_reservoir " + gas + "restore_child_gas"
loops := "ethereum.utils.numeric.taylor_exponential " + gas + "calculate_blob_gas_price"
functions := pure + " " + meter + " " + loops + " stateful.spend"
kept := meter + " " + gas + "max_message_call_gas ethereum.utils.numeric.taylor_exponential"

# Copy the pinned EELS commit into .cache/eels/<commit>.
snapshot:
    #!/usr/bin/env bash
    set -euo pipefail
    if [ ! -d "{{src}}" ]; then
      mkdir -p ".cache/eels/{{pin}}"
      git -C "{{eels}}" archive "{{pin}}" src/ethereum | tar -x -C ".cache/eels/{{pin}}"
    fi

# Translate the checked functions into lean/Eels.
gen: snapshot
    uv run python -m eels2lean --src {{src}} --src {{cases}} --out lean --pin {{pin}} --check {{functions}}

# Build the runtime, the generated Lean and the check executable.
build: gen
    cd lean && lake build EelsRuntime Eels eels-check

# Compare the Lean generated for the gas meter and the loop with tests/expected.
expected: snapshot
    rm -rf .cache/expected
    uv run python -m eels2lean --src {{src}} --out .cache/expected --pin {{pin}} {{kept}}
    diff -r tests/expected .cache/expected

# Rewrite tests/expected from the translator.
expected-update: snapshot
    rm -rf tests/expected
    uv run python -m eels2lean --src {{src}} --out tests/expected --pin {{pin}} {{kept}}

# Compare EELS Python and the generated Lean on boundary and random inputs.
check: build expected
    "{{eels}}/.venv/bin/python" -I tests/diff_check.py --src {{src}} --src {{cases}} --lean lean

# List which functions of an EELS module translate, and why the rest do not.
survey module:
    uv run python -m eels2lean --src {{src}} --survey {{module}}
