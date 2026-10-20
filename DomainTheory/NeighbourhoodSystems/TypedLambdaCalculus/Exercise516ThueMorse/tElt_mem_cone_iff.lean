module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516
public import Mathlib.Data.Nat.Bits
import all Mathlib.Data.Nat.Bits
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516ThueMorse.Basic
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516ThueMorse.iterElem_zerou27
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516ThueMorse.iterElem_succ_eq
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516ThueMorse.tmList_length
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516ThueMorse.tmList_prefix
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516ThueMorse.expand_iterate_eq
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516ThueMorse.strBot_mem_cone
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516ThueMorse.cone_univ_iff
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516ThueMorse.tmList_le_tElt

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise516

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419
















/-- **Property (a) (Scott 1981, PRG-19; Lambek).** The finite-prefix characterization of `t`: a
string `σ` is a prefix of `t` **iff** it is the length-`σ.length` Thue–Morse parity prefix. Reading
off position `n`, the `n`-th digit of `t` is `tm n`, the parity of the binary digits of `n`. -/
theorem tElt_mem_cone_iff (σ : Str) : tElt.mem (cone σ) ↔ σ = tmList σ.length := by
  constructor
  · intro hσ
    rw [show tElt = tmOp.fixElement from rfl, tmOp.fixElement_eq_iSupDirected,
      mem_iSupDirected] at hσ
    obtain ⟨n, hn⟩ := hσ
    -- `σ` is a prefix of some Thue–Morse prefix `tmList N`.
    obtain ⟨N, hpre⟩ : ∃ N, σ <+: tmList N := by
      cases n with
      | zero =>
        rw [iterElem_zero', mem_bot, C_master, cone_univ_iff] at hn
        exact ⟨0, by rw [hn]; exact List.nil_prefix⟩
      | succ k =>
        rw [iterElem_succ_eq, strBot_mem_cone, expand_iterate_eq] at hn
        exact ⟨2 ^ k, hn⟩
    -- Both `σ` and `tmList σ.length` are the length-`σ.length` prefix of `tmList N`.
    have hlen : σ.length ≤ N := hpre.length_le.trans_eq (tmList_length _)
    have h1 : σ = (tmList N).take σ.length := List.prefix_iff_eq_take.mp hpre
    have h2 : tmList σ.length = (tmList N).take σ.length := by
      have := List.prefix_iff_eq_take.mp (tmList_prefix hlen)
      rwa [tmList_length] at this
    exact h1.trans h2.symm
  · intro hσ
    have h := tmList_le_tElt σ.length
    have hmem : (strBot (tmList σ.length)).mem (cone σ) :=
      strBot_mem_cone.mpr (hσ ▸ List.prefix_rfl)
    exact h _ hmem

end DomainTheory.NeighbourhoodSystems.Exercise516
