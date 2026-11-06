module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.bot
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.constMap
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.step

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

def funSpace (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) :
    NeighborhoodSystem (ApproximableMap V₀ V₁) where
  mem W := (∃ L : List (Set α × Set β), (∀ p ∈ L, V₀.mem p.1 ∧ V₁.mem p.2) ∧ W = stepFun L)
    ∧ W.Nonempty
  master := Set.univ
  master_nonempty := ⟨constMap V₀ V₁.bot, Set.mem_univ _⟩
  master_mem := ⟨⟨[], by simp, stepFun_nil.symm⟩, ⟨constMap V₀ V₁.bot, Set.mem_univ _⟩⟩
  inter_mem := by
    rintro W W' Z ⟨⟨L, hL, rfl⟩, _⟩ ⟨⟨L', hL', rfl⟩, _⟩ ⟨_, hZne⟩ hZsub
    refine ⟨⟨L ++ L', ?_, (stepFun_append _ _).symm⟩, hZne.mono hZsub⟩
    intro p hp
    rcases List.mem_append.mp hp with h | h
    · exact hL p h
    · exact hL' p h
  sub_master := fun _ => Set.subset_univ _

@[simp] theorem funSpace_master : (funSpace V₀ V₁).master = Set.univ := rfl

theorem funSpace_mem_iff {W : Set (ApproximableMap V₀ V₁)} :
    (funSpace V₀ V₁).mem W ↔
      (∃ L : List (Set α × Set β), (∀ p ∈ L, V₀.mem p.1 ∧ V₁.mem p.2) ∧ W = stepFun L)
        ∧ W.Nonempty := Iff.rfl

theorem funSpace_mem_up_closed {W : Set (ApproximableMap V₀ V₁)} (hW : (funSpace V₀ V₁).mem W)
    {f f' : ApproximableMap V₀ V₁} (hf : f ∈ W) (hff' : f ≤ f') : f' ∈ W := by
  obtain ⟨⟨L, _, rfl⟩, _⟩ := hW
  exact stepFun_up_closed hf hff'

theorem step_mem {X : Set α} {Y : Set β} (hX : V₀.mem X) (hY : V₁.mem Y) :
    (funSpace V₀ V₁).mem (step X Y) := by
  refine ⟨⟨[(X, Y)], ?_, (stepFun_singleton X Y).symm⟩,
    ⟨constMap V₀ (V₁.principal hY), ?_⟩⟩
  · intro p hp; rw [List.mem_singleton] at hp; subst hp; exact ⟨hX, hY⟩
  · show (constMap V₀ (V₁.principal hY)).rel X Y
    exact ⟨hX, hY, subset_rfl⟩

theorem mem_stepFun_iff (φ : (funSpace V₀ V₁).Element) {L : List (Set α × Set β)}
    (hL : ∀ p ∈ L, V₀.mem p.1 ∧ V₁.mem p.2) :
    φ.mem (stepFun L) ↔ ∀ p ∈ L, φ.mem (step p.1 p.2) := by
  induction L with
  | nil => simp only [stepFun_nil, List.not_mem_nil, IsEmpty.forall_iff, implies_true, iff_true]
           exact φ.master_mem
  | cons p L ih =>
    rw [stepFun_cons]
    have hp := hL p (List.mem_cons.mpr (Or.inl rfl))
    have hLtail : ∀ q ∈ L, V₀.mem q.1 ∧ V₁.mem q.2 :=
      fun q hq => hL q (List.mem_cons.mpr (Or.inr hq))
    constructor
    · intro hmem
      have hstep : φ.mem (step p.1 p.2) :=
        φ.up_mem hmem (step_mem hp.1 hp.2) Set.inter_subset_left
      have hne : (step p.1 p.2 ∩ stepFun L).Nonempty := (φ.sub hmem).2
      have htail : φ.mem (stepFun L) :=
        φ.up_mem hmem ⟨⟨L, hLtail, rfl⟩, hne.mono Set.inter_subset_right⟩ Set.inter_subset_right
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact hstep
      · exact (ih hLtail).mp htail q hq
    · intro hall
      have hstep : φ.mem (step p.1 p.2) := hall p (List.mem_cons.mpr (Or.inl rfl))
      have htail : φ.mem (stepFun L) :=
        (ih hLtail).mpr (fun q hq => hall q (List.mem_cons.mpr (Or.inr hq)))
      exact φ.inter_mem hstep htail

end DomainTheory.NeighbourhoodSystems
