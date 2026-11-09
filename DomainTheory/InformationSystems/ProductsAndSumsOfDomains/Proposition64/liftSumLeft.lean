module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import DomainTheory.InformationSystems.ElementsOfASystem.botElement

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

variable (A : InfoSys α) (B : InfoSys β)

instance instLeftCommutativeLiftSumLeft :
    LeftCommutative fun x : α =>
      (insert (SumToken.left (β := β) x) : Finset (SumToken α β) → Finset _) :=
  ⟨fun _ _ s => insert_comm' _ _ s⟩

def liftSumLeft (v : Finset α) : Finset (SumToken α β) :=
  Multiset.foldr (fun x : α => insert (SumToken.left (β := β) x))
    (∅ : Finset (SumToken α β)) v.1

namespace liftSumLeft

theorem mem_foldr (s : Multiset α) (p : SumToken α β) :
    p ∈ Multiset.foldr (fun x : α => insert (SumToken.left (β := β) x))
        (∅ : Finset (SumToken α β)) s ↔
      ∃ x ∈ s, p = .left x := by
  refine Multiset.induction_on s ?_ ?_
  · constructor
    · intro hp
      exact False.elim (Finset.notMem_empty p hp)
    · rintro ⟨_, hx, _⟩
      exact False.elim (by cases hx)
  · intro x t ih
    simp only [Multiset.foldr_cons, Finset.mem_insert, ih, Multiset.mem_cons]
    constructor
    · rintro (hp | ⟨y, hy, hp⟩)
      · exact ⟨x, Or.inl rfl, hp⟩
      · exact ⟨y, Or.inr hy, hp⟩
    · rintro ⟨y, hy, hp⟩
      rcases hy with rfl | hy
      · exact Or.inl hp
      · exact Or.inr ⟨y, hy, hp⟩

theorem mem {v : Finset α} {p : SumToken α β} :
    p ∈ liftSumLeft (β := β) v ↔ ∃ x ∈ v, p = .left x := by
  simpa [liftSumLeft] using mem_foldr (β := β) v.1 p

theorem lftFinset_eq (v : Finset α) :
    lftFinset (liftSumLeft (β := β) v) = v := by
  ext x
  simp only [mem_lftFinset, mem]
  exact ⟨fun ⟨y, hy, h⟩ => by injection h with h'; exact h' ▸ hy,
    fun hx => ⟨x, hx, rfl⟩⟩

theorem rhtFinset_eq (v : Finset α) :
    rhtFinset (liftSumLeft (β := β) v) = ∅ := by
  ext y
  constructor
  · intro hy
    rcases mem.1 ((mem_rhtFinset).1 hy) with ⟨_, _, h⟩
    exact False.elim (nomatch h)
  · intro hy
    exact False.elim (Finset.notMem_empty y hy)

theorem con {v : Finset α} (hv : v ∈ A.Con) :
    SumCon A B (liftSumLeft (β := β) v) :=
  Or.inl ⟨by rw [lftFinset_eq]; exact hv, rhtFinset_eq (β := β) v⟩

end liftSumLeft

end InfoSys

end DomainTheory.InformationSystems
