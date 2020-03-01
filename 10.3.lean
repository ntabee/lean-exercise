instance list_has_add {α : Type*} [has_add α] : has_add (list α) := ⟨list.append⟩

#reduce [0, 2, 4] + [1, 3, 5]
