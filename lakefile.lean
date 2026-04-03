import Lake
open Lake DSL

package «recognition-science» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git "https://github.com/leanprover-community/mathlib4.git"

lean_lib RecognitionScience where
  roots := #[`RecognitionScience]

-- Canonical framework library from the Lean-formalization paper
-- (Pardo-Guerra, Simons, Thapa, Washburn, Werner 2026).
lean_lib IndisputableMonolith where
  roots := #[`IndisputableMonolith]
