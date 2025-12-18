# syntax=docker/dockerfile:1

FROM ubuntu:22.04 AS builder

ARG DEBIAN_FRONTEND=noninteractive

RUN apt-get update && apt-get install -y --no-install-recommends \
    ca-certificates \
    curl \
    git \
    xz-utils \
  && rm -rf /var/lib/apt/lists/*

WORKDIR /src

COPY lean-toolchain ./lean-toolchain

RUN curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf \
      | sh -s -- -y --default-toolchain="$(cat lean-toolchain)"

ENV PATH="/root/.elan/bin:${PATH}"

COPY . .

RUN lake update \
  && lake exe cache get \
  && lake build veribiota

FROM debian:bookworm-slim AS runtime

ARG DEBIAN_FRONTEND=noninteractive
ARG VERIBIOTA_VERSION=dev
ARG VERIBIOTA_BUILD_ID=dev

RUN apt-get update && apt-get install -y --no-install-recommends \
    ca-certificates \
    coreutils \
    openssl \
  && rm -rf /var/lib/apt/lists/*

WORKDIR /opt/veribiota

COPY --from=builder /src/.lake/build/bin/veribiota /opt/veribiota/veribiota
COPY schemas /opt/veribiota/schemas
COPY profiles/manifest.json /opt/veribiota/profiles/manifest.json
COPY LICENSE NOTICE /opt/veribiota/

ENV VERIBIOTA_DATA_DIR=/opt/veribiota
ENV VERIBIOTA_VERSION=${VERIBIOTA_VERSION}
ENV VERIBIOTA_BUILD_ID=${VERIBIOTA_BUILD_ID}

ENTRYPOINT ["/opt/veribiota/veribiota"]
