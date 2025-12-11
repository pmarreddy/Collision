#!/bin/bash
# Install Lean 4 and project dependencies

set -e

echo "=== Lean 4 Installation Script ==="

# Check OS
OS="$(uname -s)"
case "$OS" in
    Linux*)     PLATFORM=linux;;
    Darwin*)    PLATFORM=macos;;
    *)          echo "Unsupported OS: $OS"; exit 1;;
esac

echo "Detected platform: $PLATFORM"

# Check if elan is installed
if command -v elan &> /dev/null; then
    echo "elan is already installed"
    elan --version
else
    echo "Installing elan (Lean version manager)..."
    curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y

    # Add to PATH for current session
    export PATH="$HOME/.elan/bin:$PATH"
    echo "elan installed successfully"
fi

# Ensure elan is in PATH
export PATH="$HOME/.elan/bin:$PATH"

# Check if lake is available
if ! command -v lake &> /dev/null; then
    echo "Error: lake not found. Please restart your shell or run:"
    echo "  export PATH=\"\$HOME/.elan/bin:\$PATH\""
    exit 1
fi

echo "lake version: $(lake --version)"

# Navigate to project root
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(dirname "$SCRIPT_DIR")"
cd "$PROJECT_ROOT"

echo "Project root: $PROJECT_ROOT"

# Update toolchain
echo "Setting up Lean toolchain..."
if [ -f "lean-toolchain" ]; then
    TOOLCHAIN=$(cat lean-toolchain)
    echo "Using toolchain: $TOOLCHAIN"
    elan install "$TOOLCHAIN"
    elan override set "$TOOLCHAIN"
fi

# Download and build dependencies
echo "Downloading Mathlib (this may take a while on first run)..."
lake update

echo "Building project..."
lake build

echo ""
echo "=== Installation Complete ==="
echo "Run 'lake build' to rebuild the project"
echo "Run 'lake env lean <file>' to check individual files"
