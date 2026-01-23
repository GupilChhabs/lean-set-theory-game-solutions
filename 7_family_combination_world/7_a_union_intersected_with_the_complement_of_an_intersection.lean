intro x h
rw [mem_sUnion]
have hr:=h.right
rw [mem_compl_iff] at hr
rw [mem_sInter] at hr
push_neg at hr
obtain ⟨ t1,ht1⟩ := hr
obtain ⟨t2,ht2⟩ := h.left
apply Exists.intro (t2 ∩ t1ᶜ)
constructor
rw [mem_setOf]
apply Exists.intro t2
constructor
exact ht2.left
apply Exists.intro t1
constructor
exact ht1.left
rfl
constructor
exact ht2.right
exact ht1.right
