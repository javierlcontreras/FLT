import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.RepresentationTheory.Basic

universe u

open scoped TensorProduct

def Representation.GL_map_of_representation_of_basis {R V G ι: Type u} [CommRing R] [AddCommMonoid V] [Module R V]
  [Module.Free R V] [Module.Finite R V] [Group G] [DecidableEq ι] [Fintype ι]
  (ρ : Representation R G V) (𝓑 : Basis ι R V)
  : G →* Matrix.GeneralLinearGroup ι R :=
  sorry

/- Tensor product between a representation and a extension of constants -/
def Representation.tprod' {k k' : Type*} {G : Type*} {W' : Type*}
  [Monoid G]
  [CommSemiring k] [CommSemiring k'] [Algebra k' k]
  [AddCommMonoid W'] [Module k' W']
  (ρV : Representation k' G W') : Representation k G (k ⊗[k'] W')  :=
  sorry
