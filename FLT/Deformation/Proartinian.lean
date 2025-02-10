import FLT.Deformation.Algebra.InverseLimit.Basic
import FLT.Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Artinian.Module
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.RingTheory.LocalRing.Defs
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.RingTheory.AdicCompletion.Basic

universe u

namespace Deformation

variable {𝓞 : Type u} [CommRing 𝓞] [IsLocalRing 𝓞]

local notation3:max "𝓴" 𝓞 => (IsLocalRing.ResidueField 𝓞)

variable {A : Type*} [CommRing A]

variable (A) in
def ArtinianQuotientIdeal := {a : Ideal A // IsArtinianRing (A ⧸ a)}

instance : Coe (ArtinianQuotientIdeal A) (Ideal A) where
  coe a := a.1

instance : Preorder (ArtinianQuotientIdeal A) where
  le a b := (a : Ideal A) ≥ (b : Ideal A)
  lt a b := (a : Ideal A) > (b : Ideal A)
  le_refl := by simp
  le_trans := by
    rintro a b c hab hbc
    simp_all
    exact le_trans hbc hab

abbrev proartinianCompletion_obj {A : Type*} [CommRing A] (a : ArtinianQuotientIdeal A) :=
  A ⧸ (a : Ideal A)

def ideal_le_of_artinianQuotientIdeal_le {A : Type*} [CommRing A] {a b : ArtinianQuotientIdeal A}
    (h : a ≤ b) : (b : Ideal A) ≤ (a : Ideal A) :=
  by
    simp [LE.le] at h
    exact h

def proartinianCompletion_map {A : Type*} [CommRing A] {a b : ArtinianQuotientIdeal A}
    (h : a ≤ b) :
  (proartinianCompletion_obj b) →+* (proartinianCompletion_obj a) :=
    Ideal.ringHomOfQuot_of_le (ideal_le_of_artinianQuotientIdeal_le h)

abbrev proartinianCompletion (A : Type*) [CommRing A] :=
  Ring.InverseLimit
    (fun (a : ArtinianQuotientIdeal A) => proartinianCompletion_obj a)
    proartinianCompletion_map

noncomputable def diagonalMap (A : Type*) [CommRing A] : A →+* proartinianCompletion A :=
  Ring.InverseLimit.map_of_maps
    proartinianCompletion_map
    (fun a ↦ Ideal.Quotient.mk (a : Ideal A))
    (by
      rintro a b h
      unfold proartinianCompletion_map
      aesop
    )

def diagonalMap_toComponent (A : Type*) [CommRing A] (a : ArtinianQuotientIdeal A) :
  A →+* proartinianCompletion_obj a := algebraMap _ _

variable (𝓞) in
class IsProartinian (A : Type*) [CommRing A] : Prop where
  pro_artin : Function.Bijective (diagonalMap A)

namespace IsProartinian

instance (A : Type*) [CommRing A] [IsProartinian A] : TopologicalSpace A := .generateFrom
  {U | ∃ a : ArtinianQuotientIdeal A, ∃ V : Set (proartinianCompletion_obj a),
    U = (diagonalMap_toComponent A a) ⁻¹' V}

instance (A : Type*) [CommRing A] [IsProartinian A] : TopologicalRing A where
  continuous_add := sorry
  continuous_mul := sorry
  continuous_neg := sorry

instance (A : Type*) [CommRing A] [IsProartinian A] (a : Ideal A) : IsProartinian (A ⧸ a) :=
  sorry

section Noetherian -- Proposition 2.4 of Smit&Lenstra

variable (A : Type*) [CommRing A] [IsLocalRing A] [Algebra 𝓞 A]
  [IsNoetherianRing A] [IsProartinian A]

instance noetherian_topology :
  IsAdic (IsLocalRing.maximalIdeal A) := sorry

instance noetherian_isAdic :
  IsAdicComplete (IsLocalRing.maximalIdeal A) A := sorry

variable (A' : Type*) [CommRing A'] [Algebra 𝓞 A'] [IsLocalRing A'] [IsProartinian A']

lemma noetherian_continuous (f : A →ₐ[𝓞] A') : Continuous f := sorry

end Noetherian

end IsProartinian

end Deformation
