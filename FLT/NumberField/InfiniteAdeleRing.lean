import Mathlib

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

open NumberField

variable [Algebra K (InfiniteAdeleRing L)] [IsScalarTower K L (InfiniteAdeleRing L)]

-- https://leanprover.zulipchat.com/#narrow/channel/416277-FLT/topic/Functoriality.20of.20infinite.20completion.20for.20number.20fields/near/492313867
/-- The canonical map from the infinite adeles of K to the infinite adeles of L -/
noncomputable def NumberField.InfiniteAdeleRing.baseChange :
    InfiniteAdeleRing K →A[K] InfiniteAdeleRing L :=
  sorry

open scoped TensorProduct

noncomputable instance : Algebra (InfiniteAdeleRing K) (L ⊗[K] InfiniteAdeleRing K) :=
  Algebra.TensorProduct.rightAlgebra

instance : TopologicalSpace (L ⊗[K] InfiniteAdeleRing K) :=
  moduleTopology (InfiniteAdeleRing K) (L ⊗[K] InfiniteAdeleRing K)
-- TODO should be ≃A[L]
/-- The canonical `L`-algebra isomorphism from `L ⊗_K K_∞` to `L_∞` induced by the
`K`-algebra base change map `K_∞ → L_∞`. -/
def NumberField.InfiniteAdeleRing.baseChangeEquiv :
    (L ⊗[K] (InfiniteAdeleRing K)) ≃A[L] InfiniteAdeleRing L :=
  sorry