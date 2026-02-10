# Installation Guide

## Prerequisites

- Lean 4 (via elan)
- Git
- VS Code with Lean 4 extension (recommended)

## Installation Steps

1. **Install elan** (Lean version manager):
   ```bash
   curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
   elan self update
   ```

2. **Clone or extract this project**

3. **Navigate to the project directory**:
   ```bash
   cd CyclotomicFunctionFields
   ```

4. **Get cached mathlib builds** (saves hours of compilation):
   ```bash
   lake exe cache get
   ```

5. **Build the project**:
   ```bash
   lake build
   ```

6. **Open in VS Code**:
   ```bash
   code .
   ```

## Verification

To verify your setup, create a test file and check if imports work:

```lean
import CyclotomicFunctionFields.Prelude

#check Fq
#check A
#check K
```

If these compile without errors, your setup is correct!

## Troubleshooting

- If `lake exe cache get` fails, you might need to run `lake update` first
- Make sure your `lean-toolchain` file matches the version used by mathlib4
- For Windows users, make sure to use Git Bash or WSL
