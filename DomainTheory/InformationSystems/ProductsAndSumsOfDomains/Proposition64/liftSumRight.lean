module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import DomainTheory.InformationSystems.ElementsOfASystem.botElement

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

variable (A : InfoSys α) (B : InfoSys β)

instance instLeftCommutativeLiftSumRight :
    LeftCommutative fun y : β =>
      (insert (SumToken.right (α := α) y) : Finset (SumToken α β) → Finset _) :=
  ⟨fun _ _ s => insert_comm' _ _ s⟩

def liftSumRight (w : Finset β) : Finset (SumToken α β) :=
  Multiset.foldr (fun y : β => insert (SumToken.right (α := α) y))
    (∅ : Finset (SumToken α β)) w.1

namespace liftSumRight

theorem mem_foldr (s : Multiset β) (p : SumToken α β) :
    p ∈ Multiset.foldr (fun y : β => insert (SumToken.right (α := α) y))
        (∅ : Finset (SumToken α β)) s ↔
      ∃ y ∈ s, p = .right y := by
  refine Multiset.induction_on s ?_ ?_
  · constructor
    · intro hp
      exact False.elim (Finset.notMem_empty p hp)
    · rintro ⟨_, hy, _⟩
      exact False.elim (by cases hy)
  · intro y t ih
    simp only [Multiset.foldr_cons, Finset.mem_insert, ih, Multiset.mem_cons]
    constructor
    · rintro (hp | ⟨z, hz, hp⟩)
      · exact ⟨y, Or.inl rfl, hp⟩
      · exact ⟨z, Or.inr hz, hp⟩
    · rintro ⟨z, hz, hp⟩
      rcases hz with rfl | hz
      · exact Or.inl hp
      · exact Or.inr ⟨z, hz, hp⟩

theorem mem {w : Finset β} {p : SumToken α β} :
    p ∈ liftSumRight (α := α) w ↔ ∃ y ∈ w, p = .right y := by
  simpa [liftSumRight] using mem_foldr (α := α) w.1 p

theorem rhtFinset_eq (w : Finset β) :
    rhtFinset (liftSumRight (α := α) w) = w := by
  ext y
  simp only [mem_rhtFinset, mem]
  exact ⟨fun ⟨z, hz, h⟩ => by injection h with h'; exact h' ▸ hz,
    fun hy => ⟨y, hy, rfl⟩⟩

theorem lftFinset_eq (w : Finset β) :
    lftFinset (liftSumRight (α := α) w) = ∅ := by
  ext x
  constructor
  · intro hx
    rcases mem.1 ((mem_lftFinset).1 hx) with ⟨_, _, h⟩
    exact False.elim (nomatch h)
  · intro hx
    exact False.elim (Finset.notMem_empty x hx)

theorem con {w : Finset β} (hw : w ∈ B.Con) :
    SumCon A B (liftSumRight (α := α) w) :=
  Or.inr ⟨lftFinset_eq (α := α) w, by rw [rhtFinset_eq]; exact hw⟩

end liftSumRight

end InfoSys

end DomainTheory.InformationSystems
