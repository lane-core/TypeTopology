#!/usr/bin/env bash

# Function to swap characters in source code
character_swap() {
	source_file="$1"
	temp_file="temp_file.txt"
	cp "$source_file" "$temp_file"

	# Define pairs of characters to swap
	old="π"
	new="pr"

	gsed -i "s/$old/$new/g" "$temp_file"

	mv "$temp_file" "$source_file"
}

# Example usage:
# character_swap "your_source_file.txt"

for f in $@; do
	character_swap "$f"
done
