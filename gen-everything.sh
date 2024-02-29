#!/usr/bin/env bash

echo "Generating Everything.agda..."
find -iwholename './GpdCont/*.agda' \
  | sed -e 's|^\.\/||' -e 's|\.agda$||' -e 's|/|.|g' -e 's|^|import |' \
  | sort \
  | tee Everything.agda
