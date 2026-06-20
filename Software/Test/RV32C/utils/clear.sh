#!/bin/bash

cd ../

for file in *; do
    if [[ -f $file && ! $file == *.S ]]; then
        rm "$file"
    fi
done 