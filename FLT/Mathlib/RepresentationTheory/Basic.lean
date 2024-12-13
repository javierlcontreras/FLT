import Mathlib.RepresentationTheory.Basic
import FLT.Mathlib.RepresentationTheory.Subrepresentation

open scoped TensorProduct

namespace Representation

def GL_map_of_representation_of_basis {R V G ι: Type*} [CommRing R] [AddCommMonoid V] [Module R V]
  [Module.Free R V] [Module.Finite R V] [Group G] [DecidableEq ι] [Fintype ι]
  (ρ : Representation R G V) (𝓑 : Basis ι R V)
  : G →* Matrix.GeneralLinearGroup ι R :=
  sorry

variable {G : Type*} [Group G]

variable {A : Type*} [CommRing A]

variable {W : Type*} [AddCommMonoid W] [Module A W]

noncomputable def tprod' (A' : Type*) [CommRing A'] [Algebra A A']
  (ρ : Representation A G W): Representation A G (A' ⊗[A] W) := sorry

notation R "⊗ᵣ[" A "]" ρ => Representation.tprod' (A := A) R ρ
notation ρ "⊗ᵣ" ρ' => Representation.tprod ρ ρ'

class Irreducible (ρ : Representation A G W) : Prop where
  irreducible : ∀ ρ' ρ'' : Subrepresentation A G W, ∃ _ : ρ' ⊓ ρ'' = ⊥,
      ρ = ρ' ⊔ ρ'' → ρ' = ⊤ ∨ ρ'' = ⊤

class AbsolutelyIrreducible (ρ : Representation A G W) : Prop where
  absolutelyIrreducible :
    ∀ A', ∃ _ : CommRing A', ∀ _ : Algebra A A',
    Irreducible (A' ⊗ᵣ[A] ρ)

end Representation
