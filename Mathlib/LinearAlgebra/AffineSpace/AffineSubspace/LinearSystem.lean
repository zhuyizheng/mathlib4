module

public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2

open Module Submodule Matrix

def AffineSubspace.ofLinearSystem {K V : Type*} [Ring K] [AddCommGroup V] [Module K V]
    (n m : ℕ) (ι : Basis (Fin n) K V) (A : Matrix (Fin n) (Fin m) K) (b : Fin m → K) :
    AffineSubspace K V where
  carrier := {x | (ι.repr x) ᵥ* A = b}
  smul_vsub_vadd_mem := fun c p₁ p₂ p₃ hp₁ hp₂ hp₃ ↦ by
    simp only [Set.mem_setOf_eq] at hp₁ hp₂ hp₃ ⊢
    rw [vadd_eq_add, vsub_eq_sub, LinearEquiv.map_add, LinearEquiv.map_smul,
        ← LinearEquiv.coe_toLinearMap, LinearMap.map_sub,
        LinearEquiv.coe_coe, Finsupp.coe_add, Finsupp.coe_smul, Finsupp.coe_sub,
        add_vecMul, smul_vecMul, sub_vecMul,
        hp₁, hp₂, hp₃]
    simp
