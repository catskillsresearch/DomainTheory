module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.InformationSystems.Proposition23
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.BasicInst5
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.ProdToken
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.BasicInst7
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.prodBot
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.instLeftCommutativeFstInsert
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.instLeftCommutativeSndInsert
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.fstFinset
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.sndFinset
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.ProdCon
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.ProdEnt

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

variable (A : InfoSys α) (B : InfoSys β)

def productSystem : InfoSys (ProdToken A B) where
  bot := prodBot A B
  Con := {u | ProdCon A B u}
  Ent := ProdEnt A B
  con_subset := by
    intro u v hu hv
    exact ⟨A.con_subset hu.1 (fstFinset.mono A B hv),
      B.con_subset hu.2 (sndFinset.mono A B hv)⟩
  con_sing := by
    intro p
    refine ⟨?_, ?_⟩
    · rcases p.property.out with h1 | h2
      · by_cases h2 : p.val.2 = B.bot
        · have hpeq : p = prodBot A B := Subtype.ext (Prod.ext h1 h2)
          subst hpeq
          rw [fstFinset.singleton_left A B (prodBot A B) rfl]
          exact A.con_sing A.bot
        · have hfst : fstFinset A B {p} = ∅ := by
            ext x
            constructor
            · intro hx
              rcases (mem_fstFinset A B).1 hx with ⟨q, hq, hbot', _⟩
              have hq' : q = p := Finset.mem_singleton.mp hq
              subst hq'
              exact False.elim (h2 hbot')
            · intro hx
              exact False.elim (Finset.notMem_empty x hx)
          rw [hfst]
          exact A.con_empty
      · rw [fstFinset.singleton_left A B p h2]
        exact A.con_sing p.val.1
    · rcases p.property.out with h1 | h2
      · rw [sndFinset.singleton_right A B p h1]
        exact B.con_sing p.val.2
      · by_cases h1 : p.val.1 = A.bot
        · have hpeq : p = prodBot A B := Subtype.ext (Prod.ext h1 h2)
          subst hpeq
          rw [sndFinset.singleton_right A B (prodBot A B) rfl]
          exact B.con_sing B.bot
        · have hsnd : sndFinset A B {p} = ∅ := by
            ext y
            constructor
            · intro hy
              rcases (mem_sndFinset A B).1 hy with ⟨q, hq, hbot', _⟩
              have hq' : q = p := Finset.mem_singleton.mp hq
              subst hq'
              exact False.elim (h1 hbot')
            · intro hy
              exact False.elim (Finset.notMem_empty y hy)
          rw [hsnd]
          exact B.con_empty
  ent_con := by
    intro u p ⟨⟨hfst, hsnd⟩, hL, hR⟩
    refine ⟨?_, ?_⟩
    · by_cases hp2 : p.val.2 = B.bot
      · rw [fstFinset.insert_left A B u p hp2]
        exact A.ent_con (hL hp2)
      · rw [fstFinset.insert_not_left A B u p hp2]
        exact hfst
    · by_cases hp1 : p.val.1 = A.bot
      · rw [sndFinset.insert_right A B u p hp1]
        exact B.ent_con (hR hp1)
      · rw [sndFinset.insert_not_right A B u p hp1]
        exact hsnd
  ent_bot := by
    intro u hu
    exact ⟨hu, fun _ => A.ent_bot hu.1, fun _ => B.ent_bot hu.2⟩
  ent_refl := by
    intro u p hu hp
    refine ⟨hu, ?_, ?_⟩
    · intro hbot
      exact A.ent_refl hu.1 ((mem_fstFinset A B).2 ⟨p, hp, hbot, rfl⟩)
    · intro hbot
      exact B.ent_refl hu.2 ((mem_sndFinset A B).2 ⟨p, hp, hbot, rfl⟩)
  ent_trans := by
    intro u v c hv hu hEnts hEntc
    refine ⟨hv, ?_, ?_⟩
    · intro hbot
      have hfst : ∀ y ∈ fstFinset A B u, A.Ent (fstFinset A B v) y := by
        intro y hy
        rcases (mem_fstFinset A B).1 hy with ⟨q, hq, hq2, rfl⟩
        exact (hEnts q hq).2.1 hq2
      exact A.ent_trans hv.1 hu.1 hfst (hEntc.2.1 hbot)
    · intro hbot
      have hsnd : ∀ y ∈ sndFinset A B u, B.Ent (sndFinset A B v) y := by
        intro y hy
        rcases (mem_sndFinset A B).1 hy with ⟨q, hq, hq1, rfl⟩
        exact (hEnts q hq).2.2 hq1
      exact B.ent_trans hv.2 hu.2 hsnd (hEntc.2.2 hbot)

end InfoSys

end DomainTheory.InformationSystems
