# Contributing to CyclotomicFunctionFields

Thank you for your interest in contributing!

## How to Contribute

1. **Pick an issue or create one**
   - Look for issues labeled "good first issue"
   - Create an issue for new features or bugs

2. **Fork and clone**
   ```bash
   git clone <your-fork-url>
   cd CyclotomicFunctionFields
   ```

3. **Create a branch**
   ```bash
   git checkout -b my-feature
   ```

4. **Make your changes**
   - Follow the development guide
   - Add tests where appropriate
   - Update documentation

5. **Test your changes**
   ```bash
   lake build
   ```

6. **Commit and push**
   ```bash
   git add -A
   git commit -m "Description of changes"
   git push origin my-feature
   ```

7. **Create a pull request**

## Code Style

- Follow mathlib4 conventions
- Use descriptive names
- Add docstrings to all definitions
- Reference Hayes' paper with section numbers
- Keep proofs readable

## Documentation

- Every `def` and `theorem` should have a docstring
- Use `/-! ... -/` for module-level documentation
- Use `/-- ... -/` for definition-level documentation
- Include examples where helpful

## Testing

- Add examples to `Examples.lean`
- Verify your proofs compile
- Check that imports are minimal

## Questions?

- Open an issue
- Ask on Zulip: https://leanprover.zulipchat.com/
