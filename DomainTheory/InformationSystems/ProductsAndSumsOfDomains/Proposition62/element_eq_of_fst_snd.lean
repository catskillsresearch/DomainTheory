/-ai
Two elements of the product system that have the same image under the first projection and the same image under the second projection are equal. This is Scott's uniqueness lemma for product elements.

The two inclusions of the element order are symmetric. Given a token p of the first element, the singleton of p lies in that element and is therefore product-consistent. If p is right-tagged or bottom, reflexivity in B puts its second component in the second projection of the first element, hence of the second element. A consistent set in the second element then entails that component, and rebuilding product entailment with the bottom entailment on the first component and that entailment on the second puts p in the second element by closure. If p is left-tagged, the same argument uses the first projection, reflexivity in A, and the bottom entailment on the second component.
ai-/
module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition53
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition62.Basic

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
variable (A : InfoSys α) (B : InfoSys β)


namespace ApproximableMap

variable {C : InfoSys γ}


/-- Product elements are determined by their projections (Scott’s uniqueness lemma). -/
theorem element_eq_of_fst_snd (z z' : (productSystem A B).Element)
    (hfst : (fstMap A B).toElement z = (fstMap A B).toElement z')
    (hsnd : (sndMap A B).toElement z = (sndMap A B).toElement z') :
    z = z' := by
  apply le_antisymm
  · intro p hp
    have hpz : (↑({p} : Finset (ProdToken A B)) : Set _) ⊆ z.carrier := by
      intro q hq
      have : q = p := Finset.mem_singleton.mp (Finset.mem_coe.1 hq)
      subst this
      exact hp
    have hCon : ProdCon A B {p} := z.consistent {p} hpz
    rcases p.property with h1 | h2
    · -- right-tagged (or bottom): use `snd`
      have hy : p.val.2 ∈ ((sndMap A B).toElement z).carrier := by
        refine ⟨{p}, hpz, ?_⟩
        refine ⟨hCon, B.con_sing p.val.2, ?_⟩
        intro y hy
        have : y = p.val.2 := Finset.mem_singleton.mp hy
        subst this
        exact B.ent_refl hCon.2 ((mem_sndFinset A B).2 ⟨p, Finset.mem_singleton_self p, h1, rfl⟩)
      have hy' : p.val.2 ∈ ((sndMap A B).toElement z').carrier := by
        rw [← hsnd]
        exact hy
      rcases hy' with ⟨u, hu, ⟨huCon, _, hEnt⟩⟩
      have hEntp : (productSystem A B).Ent u p := by
        refine ⟨huCon, ?_, ?_⟩
        · intro _
          simpa [h1] using A.ent_bot huCon.1
        · intro _
          exact hEnt p.val.2 (Finset.mem_singleton_self _)
      exact z'.closed u p hu hEntp
    · -- left-tagged: use `fst`
      have hx : p.val.1 ∈ ((fstMap A B).toElement z).carrier := by
        refine ⟨{p}, hpz, ?_⟩
        refine ⟨hCon, A.con_sing p.val.1, ?_⟩
        intro x hx
        have : x = p.val.1 := Finset.mem_singleton.mp hx
        subst this
        exact A.ent_refl hCon.1 ((mem_fstFinset A B).2 ⟨p, Finset.mem_singleton_self p, h2, rfl⟩)
      have hx' : p.val.1 ∈ ((fstMap A B).toElement z').carrier := by
        rw [← hfst]
        exact hx
      rcases hx' with ⟨u, hu, ⟨huCon, _, hEnt⟩⟩
      have hEntp : (productSystem A B).Ent u p := by
        refine ⟨huCon, ?_, ?_⟩
        · intro _
          exact hEnt p.val.1 (Finset.mem_singleton_self _)
        · intro _
          simpa [h2] using B.ent_bot huCon.2
      exact z'.closed u p hu hEntp
  · intro p hp
    have hpz : (↑({p} : Finset (ProdToken A B)) : Set _) ⊆ z'.carrier := by
      intro q hq
      have : q = p := Finset.mem_singleton.mp (Finset.mem_coe.1 hq)
      subst this
      exact hp
    have hCon : ProdCon A B {p} := z'.consistent {p} hpz
    rcases p.property with h1 | h2
    · have hy : p.val.2 ∈ ((sndMap A B).toElement z').carrier := by
        refine ⟨{p}, hpz, ?_⟩
        refine ⟨hCon, B.con_sing p.val.2, ?_⟩
        intro y hy
        have : y = p.val.2 := Finset.mem_singleton.mp hy
        subst this
        exact B.ent_refl hCon.2 ((mem_sndFinset A B).2 ⟨p, Finset.mem_singleton_self p, h1, rfl⟩)
      have hy' : p.val.2 ∈ ((sndMap A B).toElement z).carrier := by
        rw [hsnd]
        exact hy
      rcases hy' with ⟨u, hu, ⟨huCon, _, hEnt⟩⟩
      have hEntp : (productSystem A B).Ent u p := by
        refine ⟨huCon, ?_, ?_⟩
        · intro _
          simpa [h1] using A.ent_bot huCon.1
        · intro _
          exact hEnt p.val.2 (Finset.mem_singleton_self _)
      exact z.closed u p hu hEntp
    · have hx : p.val.1 ∈ ((fstMap A B).toElement z').carrier := by
        refine ⟨{p}, hpz, ?_⟩
        refine ⟨hCon, A.con_sing p.val.1, ?_⟩
        intro x hx
        have : x = p.val.1 := Finset.mem_singleton.mp hx
        subst this
        exact A.ent_refl hCon.1 ((mem_fstFinset A B).2 ⟨p, Finset.mem_singleton_self p, h2, rfl⟩)
      have hx' : p.val.1 ∈ ((fstMap A B).toElement z).carrier := by
        rw [hfst]
        exact hx
      rcases hx' with ⟨u, hu, ⟨huCon, _, hEnt⟩⟩
      have hEntp : (productSystem A B).Ent u p := by
        refine ⟨huCon, ?_, ?_⟩
        · intro _
          exact hEnt p.val.1 (Finset.mem_singleton_self _)
        · intro _
          simpa [h2] using B.ent_bot huCon.2
      exact z.closed u p hu hEntp

end ApproximableMap
end InfoSys
end DomainTheory.InformationSystems
