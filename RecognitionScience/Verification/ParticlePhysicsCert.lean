import Mathlib
-- import RecognitionScience.Verification.CKMCert  -- [not in public release]
import RecognitionScience.Verification.NeutrinoSectorCert

/-!
# Particle Physics Certificate (publishable surface)

This module defines the **publishable particle sector** as exactly the conjunction of:

- `Verification.CKMCert` (CKM sector)
- `Verification.NeutrinoSectorCert` (neutrino masses + PMNS angles + Jarlskog)

Design choice (important):
- We **do not** require an explicit construction/existence theorem of a global PMNS
  unitary matrix realizing a specific weight tensor. That existence statement is
  currently quarantined as a conjecture (`Physics/PMNS/Construction.lean`) and is
  *not* needed for the hard‑falsifiable numeric claims bundled here.
-/

namespace RecognitionScience
namespace Verification
namespace ParticlePhysicsCert

def Publishable : Prop :=
  CKMCert.Cert ∧ NeutrinoSectorCert.Cert

theorem publishable : Publishable :=
  ⟨CKMCert.cert, NeutrinoSectorCert.cert⟩

end ParticlePhysicsCert
end Verification
end RecognitionScience
