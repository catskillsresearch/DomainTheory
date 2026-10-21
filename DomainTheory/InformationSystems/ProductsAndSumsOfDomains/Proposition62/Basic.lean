/-ai
A product token lies in the fold that inserts left injections of a multiset of tokens of the first system, starting from the empty set, if and only if it is the left injection of some member of the multiset.

The proof is by induction on the multiset. For the empty multiset, both a member of the empty set and a member of the multiset are impossible. At a cons cell, membership in the inserted fold is equality with the injected head or membership in the fold of the tail, and the inductive equivalence matches that alternative with membership of the witness in the cons.

A product token lies in the fold that inserts right injections of a multiset of tokens of the second system, starting from the empty set, if and only if it is the right injection of some member of the multiset.

The proof is the same induction, with the right injection in place of the left injection.

If an approximable map relates a consistent finite set s to the empty set, then it relates s to every finite set contained in the singleton of the least token.

That finite set is consistent by downward closure of the consistent singleton. The empty set set-entails it, because each of its members equals the least token and the empty set entails the least token. Monotonicity of the approximable relation then enlarges the empty related set, using reflexivity of set-entailment on s.

The same statement holds with the roles of the two factors exchanged: a map that relates s to the empty set of the first system relates s to every subset of the singleton of that system's least token.

The argument is the same, with consistency, entailment of the least token, and monotonicity taken in the first system.
ai-/
module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition53
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition62.mkLeft
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition62.mkRight
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition62.liftLeft
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition62.liftRight
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition62.fstMap
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition62.sndMap
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition62.pairMap
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition62.instLeftCommutativeMkLeftInsert
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition62.instLeftCommutativeMkRightInsert
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition62.ProdCon_empty
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition62.entSet_fst_of_prodEntSet
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition62.entSet_snd_of_prodEntSet

@[expose] public section

/-!
# Proposition 6.2 — product projections and pairing

**Scott 1982, Proposition 6.2.** Approximable `fst`, `snd`, and unique pairing
`⟨f, g⟩` with `fst ∘ ⟨f, g⟩ = f` and `snd ∘ ⟨f, g⟩ = g`.
-/

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
variable (A : InfoSys α) (B : InfoSys β)


theorem mem_foldr_liftLeft (s : Multiset α) (p : ProdToken A B) :
    p ∈ Multiset.foldr (fun x : α => insert (mkLeft A B x)) (∅ : Finset (ProdToken A B)) s ↔
      ∃ x ∈ s, p = mkLeft A B x := by
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

theorem mem_foldr_liftRight (s : Multiset β) (p : ProdToken A B) :
    p ∈ Multiset.foldr (fun y : β => insert (mkRight A B y)) (∅ : Finset (ProdToken A B)) s ↔
      ∃ y ∈ s, p = mkRight A B y := by
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


namespace ApproximableMap

variable {C : InfoSys γ}


/-- Helper: `g` relates `s` to any subset of `{Δ_B}` once it relates to `∅`. -/
theorem rel_bot_subset {D : InfoSys β} {s : Finset γ} {w : Finset β}
    (g : ApproximableMap C D) (hs : s ∈ C.Con)
    (hg : g.rel s (∅ : Finset β)) (hw : w ⊆ ({D.bot} : Finset β)) :
    g.rel s w := by
  have hwCon : w ∈ D.Con := D.con_subset (D.con_sing D.bot) hw
  have hEnt : D.EntSet (∅ : Finset β) w := by
    intro y hy
    have : y = D.bot := Finset.mem_singleton.mp (hw hy)
    subst this
    exact D.ent_bot D.con_empty
  exact g.mono hg (proposition_2_3_iii C hs) hEnt hs hwCon

/-- Helper: `f` relates `s` to any subset of `{Δ_A}` once it relates to `∅`. -/
theorem rel_bot_subset_left {D : InfoSys α} {s : Finset γ} {v : Finset α}
    (f : ApproximableMap C D) (hs : s ∈ C.Con)
    (hf : f.rel s (∅ : Finset α)) (hv : v ⊆ ({D.bot} : Finset α)) :
    f.rel s v := by
  have hvCon : v ∈ D.Con := D.con_subset (D.con_sing D.bot) hv
  have hEnt : D.EntSet (∅ : Finset α) v := by
    intro x hx
    have : x = D.bot := Finset.mem_singleton.mp (hv hx)
    subst this
    exact D.ent_bot D.con_empty
  exact f.mono hf (proposition_2_3_iii C hs) hEnt hs hvCon

end ApproximableMap
end InfoSys
end DomainTheory.InformationSystems
