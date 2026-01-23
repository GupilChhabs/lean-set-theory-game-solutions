intro x h2
rw [mem_sUnion]
obtain ⟨ t,ht ⟩ := h2.left
by_cases h : t ∈ G
apply Exists.intro t
constructor
exact And.intro ht.left h
exact ht.right
have h3: x ∈ ⋃₀ (  F∩Gᶜ)
apply Exists.intro t
constructor
constructor
exact ht.left
by_contra h3
rw [mem_compl_iff] at h3
push_neg at h3
exact h h3
exact ht.right
have h4 := h1 h3
have h4r:= h4.right
rw [mem_compl_iff] at h4r
by_contra h5
exact h4r h2.right
