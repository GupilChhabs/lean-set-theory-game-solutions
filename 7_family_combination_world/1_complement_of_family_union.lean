ext x
apply Iff.intro
intro h
rw [mem_sInter]
intro t h1
rw [mem_setOf] at h1
rw [mem_compl_iff] at h
rw [mem_sUnion] at h
push_neg at h
have h2 : x ∉ tᶜ := h tᶜ  h1
rw [mem_compl_iff] at h2
push_neg at h2
exact h2
intro h
rw [mem_sInter] at h
rw [mem_compl_iff]
by_contra h1
rw [mem_sUnion] at h1
obtain ⟨ t,ht⟩ := h1
apply h tᶜ
rw [mem_setOf]
rw [compl_compl]
exact ht.left
exact ht.right
