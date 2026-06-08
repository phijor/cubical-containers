#!/usr/bin/env bash

echo "Generating Everything.agda..."
git ls-files \
  | grep 'GpdCont/.*\.agda' \
  | sed -e 's|\.agda$||' -e 's|/|.|g' -e 's|^|import |' \
  | sort \
  | tee Everything.agda
