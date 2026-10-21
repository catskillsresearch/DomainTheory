/-ai
A filter of the strict function space contains the step-function set of a list of neighbourhood pairs exactly when it contains the step set of every pair in the list.

The proof is by induction on the list. The empty step-function set is the master neighbourhood, which belongs to the filter. For a list with a head pair, that set is the intersection of the head step with the step-function set of the tail. From membership of the intersection, a witness in the intersection makes the head step a neighbourhood, and upward closure along the two inclusions puts both the head step and the tail set into the filter; the inductive hypothesis splits the tail. In the other direction the two pieces belong to the filter by the hypothesis and the inductive hypothesis, and the filter is closed under intersection.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smash_master
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.smash_mem_bot
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.mem_smashPair
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.mono
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.sstep
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.mem_sstep
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.sstepFun
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.mem_sstepFun
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.sstepFun_nil
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.sstepFun_cons
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.sstep_master_eq
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.strictFun
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.strictFun_master
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510.sstep_mem_of_mem

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise510

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- The generation lemma: a filter contains `sstepFun L` iff it contains each step `[Xᵢ, Yᵢ]`. -/
theorem mem_sstepFun_iff (φ : (strictFun V₀ V₁).Element) {L : List (Set α × Set β)}
    (hL : ∀ p ∈ L, V₀.mem p.1 ∧ V₁.mem p.2) :
    φ.mem (sstepFun L) ↔ ∀ p ∈ L, φ.mem (sstep p.1 p.2) := by
  induction L with
  | nil => simp only [sstepFun_nil, List.not_mem_nil, IsEmpty.forall_iff, implies_true, iff_true]
           exact φ.master_mem
  | cons p L ih =>
    rw [sstepFun_cons]
    have hLtail : ∀ q ∈ L, V₀.mem q.1 ∧ V₁.mem q.2 :=
      fun q hq => hL q (List.mem_cons.mpr (Or.inr hq))
    constructor
    · intro hmem
      obtain ⟨g, hg⟩ := (φ.sub hmem).2
      have hstep : φ.mem (sstep p.1 p.2) :=
        φ.up_mem hmem (sstep_mem_of_mem (g := g) (hg.1)) Set.inter_subset_left
      have hne : (sstep p.1 p.2 ∩ sstepFun L).Nonempty := (φ.sub hmem).2
      have htail : φ.mem (sstepFun L) :=
        φ.up_mem hmem ⟨⟨L, hLtail, rfl⟩, hne.mono Set.inter_subset_right⟩ Set.inter_subset_right
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact hstep
      · exact (ih hLtail).mp htail q hq
    · intro hall
      have hstep : φ.mem (sstep p.1 p.2) := hall p (List.mem_cons.mpr (Or.inl rfl))
      have htail : φ.mem (sstepFun L) :=
        (ih hLtail).mpr (fun q hq => hall q (List.mem_cons.mpr (Or.inr hq)))
      exact φ.inter_mem hstep htail

end DomainTheory.NeighbourhoodSystems.Exercise510
