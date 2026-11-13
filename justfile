pin := `grep '^commit' eels.toml | cut -d'"' -f2`
eels := env("EELS", home_directory() / "ethereum/execution-specs")
src := ".cache/eels" / pin / "src"
cases := "tests/cases"
gas := "ethereum.forks.amsterdam.vm.gas."
pure := gas + "max_message_call_gas " + gas + "calculate_memory_gas_cost " + gas + "init_code_cost ethereum.utils.numeric.ceil32 " + gas + "calculate_message_call_gas " + gas + "allocate_evm_gas"
meter := gas + "charge_gas_from_meter " + gas + "charge_state_gas_from_meter " + gas + "commit_state_gas " + gas + "restore_state_gas " + gas + "restore_state_gas_to_entry " + gas + "tx_state_gas_used " + gas + "credit_state_gas_refund " + gas + "repay_state_gas_spill " + gas + "forfeit_remaining_gas " + gas + "withhold_create_gas " + gas + "drain_state_gas_reservoir " + gas + "restore_child_gas"
functions := pure + " " + meter + " stateful.spend"

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

# Compare EELS Python and the generated Lean on boundary and random inputs.
check: build
    "{{eels}}/.venv/bin/python" -I tests/diff_check.py --src {{src}} --src {{cases}} --lean lean

# List which functions of an EELS module translate, and why the rest do not.
survey module:
    uv run python -m eels2lean --src {{src}} --survey {{module}}
