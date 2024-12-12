import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.RepresentationTheory.Basic

universe u

def GL_map_of_representation_of_basis {R V G ι: Type u} [CommRing R] [AddCommMonoid V] [Module R V]
  [Module.Free R V] [Module.Finite R V] [Group G] [DecidableEq ι] [Fintype ι]
  (ρ : Representation R G V) (𝓑 : Basis ι R V)
  : G →* Matrix.GeneralLinearGroup ι R :=
  sorry

#min_imports
