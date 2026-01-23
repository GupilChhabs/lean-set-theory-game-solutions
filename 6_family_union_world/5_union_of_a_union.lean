ext x
apply Iff.intro
intro h
rw [mem_sUnion] at h
obtain ⟨ w ,hw ⟩  := h
rcases hw with hf|hg
left
rw [mem_sUnion]
apply Exists.intro w
exact And.intro hf right
right
apply Exists.intro w
exact And.intro hg right
intro h
rw [mem_sUnion]
rcases h with hf|hg
rw [mem_sUnion] at hf
obtain ⟨ t ,ht ⟩ := hf
apply Exists.intro t
constructor
left
exact ht.left
exact ht.right
obtain ⟨ t,ht⟩ := hg
apply Exists.intro t
constructor
right
exact ht.left
exact ht.right
