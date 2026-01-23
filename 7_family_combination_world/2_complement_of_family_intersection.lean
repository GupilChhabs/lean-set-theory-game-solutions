ext x
apply Iff.intro
intro h
rw [mem_sUnion]
rw [mem_compl_iff] at h
rw [mem_sInter] at h
push_neg at h
obtain ⟨t,ht ⟩:= h
apply Exists.intro tᶜ
constructor
rw [mem_setOf]
rw [compl_compl]
exact ht.left
exact ht.right
intro h
rw [mem_compl_iff]
by_contra
rw [mem_sUnion] at h
obtain ⟨t,ht⟩ := h
rw [mem_sInter] at a
have htl:= ht.left
rw [mem_setOf] at htl
have h1: x ∈ tᶜ := a tᶜ htl
exact h1 ht.right
