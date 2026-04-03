import Lake
open Lake DSL

package «recognition-science» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git "https://github.com/leanprover-community/mathlib4.git"

lean_lib RecognitionScience where
  roots := #[`RecognitionScience]
