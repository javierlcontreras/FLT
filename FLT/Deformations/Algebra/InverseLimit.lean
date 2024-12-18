import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.FreeCommRing
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.Tactic.SuppressCompilation
import Mathlib.Order.DirectedInverseSystem

/-!
# Inverse limit of modules, abelian groups, rings.

See Atiyah-Macdonald PP.32-33, Matsumura PP.269-270

## Main definitions

* `Module.InverseLimit G f`
* `AddCommGroup.InverseLimit G f`
* `Ring.InverseLimit G f`
-/

namespace Module

variable {ι : Type*} [Preorder ι]

variable {object : ι → Type*}
        {R : Type*} [Ring R]
        [∀ i, AddCommGroup (object i)]
        [∀ i, Module R (object i)]
        (map : ⦃i j : ι⦄ → (h : i ≤ j) → object j →ₗ[R] object i)
        [InverseSystem (fun _ _ hij ↦ map hij)]

/-- The inverse limit of an inverse system is the modules glued together along the maps. -/
def InverseLimit : Set (Π i : ι, object i) :=
  Submodule.span R <| { a : Π i : ι, object i | ∀ (i j : _) (h : i ≤ j), map h (a j) = a i }

namespace InverseLimit

section Basic

variable [DecidableEq ι]

instance addCommGroup : AddCommGroup (InverseLimit map) := by
  unfold InverseLimit
  infer_instance

instance module : Module R (InverseLimit map) := by
  unfold InverseLimit
  infer_instance

instance inhabited : Inhabited (InverseLimit map) :=
  ⟨0⟩

instance unique [IsEmpty ι] : Unique (InverseLimit map) := by
  unfold InverseLimit
  simp
  sorry

/-- The canonical map from the inverse limit to the i-th component. -/
def toComponent (i : ι) : InverseLimit map →ₗ[R] object i := sorry

@[simp]
lemma toComponent_map {i j : ι} {hij : i ≤ j} {x : InverseLimit map}: map hij (toComponent map j x) =
  toComponent map i x := sorry

end Basic

end InverseLimit

end Module

namespace AddCommGroup

end AddCommGroup

namespace Ring

end Ring

namespace Field

end Field
