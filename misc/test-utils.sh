#!/usr/bin/env bash

# NOTE(wmuth, 2025-03-25): This function expects 1 param which is "$@"
ensure_mi_exists() {
  local BOOTSTRAPPED="false"
  local CHEATED="false"
  local INSTALLED="false"

  for arg in $@; do
    if [ "$arg" == "--bootstrapped" ]; then
      BOOTSTRAPPED="true"
    elif [ "$arg" == "--cheated" ]; then
      CHEATED="true"
    elif [ "$arg" == "--installed" ]; then
      INSTALLED="true"
    fi
  done

  if [ "$BOOTSTRAPPED" == "false" ] && [ "$CHEATED" == "false" ] && [ "$INSTALLED" == "false" ]; then
    CHEATED="true"
  fi

  if [ "$BOOTSTRAPPED" == "true" ]; then
    if ! [ -f "$DIR/build/mi" ]; then
      echo "'mi' is not bootstrapped. Bootstrapping... "
      make -C "$DIR" bootstrap || {
        echo "Bootstrapping 'mi' failed."
        exit 1
      }
      echo "Bootstrapping complete."
    fi
  fi

  if [ "$CHEATED" == "true" ]; then
    if ! [ -f "$DIR/build/mi-cheat" ]; then
      echo "'mi-cheat' does not exist. Trying to compile..."
      make -C "$DIR" cheat || {
        echo "Compiling 'mi-cheat' failed."
        exit 1
      }
      echo "Compiled 'mi-cheat'."
    fi
  fi

  if [ "$INSTALLED" == "true" ]; then
    if ! command -v mi >/dev/null 2>&1; then
      echo "'mi' is not installed. Installing... "
      make -C "$DIR" install || {
        echo "Installing 'mi' failed."
        exit 1
      }
      echo "Installed 'mi'."
    fi
  fi
}
