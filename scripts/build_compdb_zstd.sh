#!/usr/bin/env bash
make clean
sed -i 's/zstd : CPPFLAGS += -DZSTD_LEGACY_SUPPORT=$(ZSTD_LEGACY_SUPPORT).*/zstd : CPPFLAGS += -DZSTD_LEGACY_SUPPORT=$(ZSTD_LEGACY_SUPPORT) -DZSTD_NO_INTRINSICS/' programs/Makefile
bear -- make -j 1 zstd