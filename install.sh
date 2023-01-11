#!/bin/sh

# Installation script for MPC
# Copyright (c) 2022-2023, Mate Kukri
# SPDX-License-Identifier: GPL-2.0-only

# Exit on error
set -e

# Default installation prefix
PREFIX=${PREFIX:-/usr/local}

# Change into the directory we meant to be in
cd "$(dirname "$0")"

# Installation paths
MPC_BIN_DIR="$PREFIX/bin"
MPC_STD_DIR="$PREFIX/share/mpc"
export MPC_STD_DIR

# Build mpc
cargo build --release --bin mpc

# Create directories
install -d "$MPC_BIN_DIR"
install -d "$MPC_STD_DIR"

# Install mpc
install target/release/mpc "$MPC_BIN_DIR"

# Install mpc_std
for file in mpc_std/*
do
  install "$file" "$MPC_STD_DIR"
done
