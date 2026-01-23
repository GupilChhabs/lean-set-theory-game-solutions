ext x
apply Iff.intro
intro h
rcases h with ha|hb
rw [mem_sUnion]
apply Exists.intro A
constructor
rw [mem_pair]
left
rfl
exact ha
rw [mem_sUnion]
apply Exists.intro B
constructor
rw [mem_pair]
right
rfl
exact hb
intro h
rw [mem_sUnion] at h
obtain ⟨  w , hA ⟩  := h
rw [mem_pair] at hA
rcases hA with hA1|hA2
left
rw [hA1] at right
exact right
rw [hA2] at right
right
exact right
