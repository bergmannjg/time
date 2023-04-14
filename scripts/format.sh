#!/usr/bin/env bash
# minimal format

if [ ! -d "./scripts" ]; then
    echo "please run from project directory"
    exit 1
fi

find . -name "*.lean" -not -path "*/lake-packages/*" \
    -exec sed -i '/!/!s/\([a-z)]\):\([^/]\)/\1 :\2/g' {} \; \
    -exec sed -i 's/:\([A-Z]\)/: \1/g' {} \; \
    -exec sed -i 's/  :/ :/g' {} \; \
    -exec sed -i 's/:  /: /g' {} \;
