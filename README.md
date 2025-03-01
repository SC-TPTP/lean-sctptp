# Lean SC-TPTP

Lean SC-TPTP brings a new interface between Lean 4 and automated theorem provers following the SC-TPTP format. In particular, Lean SC-TPTP introduces tactics doing proof reconstruction end-to-end by performing the following steps:

- **Monomorphize the problem:** All dependently-typed/universe-polymorphic problems are monomorphized.
- **Translate to TPTP FOF:** The monomorphized problem is converted into the TPTP FOF (first-order) format.
- **Run the solver:** The tactic invokes either the Egg or Goeland solver on the translated problem.
- **Obtain the SC-TPTP proof:** The resulting proof is returned in the SC-TPTP format.
- **Parse and reify:** The proof is parsed, reified, and then reconstructed in Lean 4 using Lean’s built-in tactics.

This codebase builds upon the [Lean Auto](https://github.com/leanprover/lean-auto) work. In particular, you may refer to the second part of the [Tactic.lean](Auto/Tactic.lean) file along with [TPTP.lean](Auto/Parser/TPTP.lean) and [TPTP_FOF.lean](Auto/IR/TPTP_FOF.lean) for more detailed insights on solver integrations and proof reconstruction.

## Usage

At the moment, two solvers are available: `Egg` and `Goeland` through the `egg` and `goeland` tactics, respectively. To use these new tactics, simply set the following desired options:

- `set_option auto.tptp true`
- `set_option auto.tptp.egg.path "/path/to/egg-sc-tptp"`
- `set_option auto.tptp.goeland.path "/path/to/goeland_linux_release"`
- `set_option auto.mono.mode "fol"`
and invoke either `egg` or  `goeland` in your proofs. The tactics will perform all the steps mentioned above. Examples are available at the end of the [Tactic.lean](Auto/Tactic.lean) file.

Adding new solvers is straightforward as long as they support the SC-TPTP format. Simply add a new tactic at the end of the [Tactic.lean](Auto/Tactic.lean) file.

## Requirements

- Lean 4
- Executables for the corresponding solvers with SC-TPTP support.

## Acknowledgements

Lean SC-TPTP builds upon the pioneering work of Lean Auto. Contributions and suggestions are welcome!
