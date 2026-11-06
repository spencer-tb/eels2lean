pin := `grep '^commit' eels.toml | cut -d'"' -f2`
eels := env("EELS", home_directory() / "ethereum/execution-specs")
src := ".cache/eels" / pin / "src"
functions := "ethereum.forks.amsterdam.vm.gas.max_message_call_gas ethereum.forks.amsterdam.vm.gas.calculate_memory_gas_cost ethereum.forks.amsterdam.vm.gas.init_code_cost ethereum.utils.numeric.ceil32"

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
    uv run python -m eels2lean --src {{src}} --out lean --pin {{pin}} --check {{functions}}

# Build the runtime, the generated Lean and the check executable.
build: gen
    cd lean && lake build EelsRuntime Eels eels-check

# Compare EELS Python and the generated Lean on boundary and random inputs.
check: build
    "{{eels}}/.venv/bin/python" -I tests/diff_check.py --src {{src}} --lean lean

# List which functions of an EELS module translate, and why the rest do not.
survey module:
    uv run python -m eels2lean --src {{src}} --survey {{module}}
