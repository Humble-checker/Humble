# Builds the Isabelle theories and Humble, and exports generated/ and build/:
#
#   docker build --output type=local,dest=out .
#
# The Isabelle release comes from versions.cmake; the AFP from AFP_URL (by default the development
# snapshot, which is what a release candidate needs). Isabelle-LLVM is the isabelle_llvm submodule,
# so run `git submodule update --init` first.

FROM ubuntu:26.04 AS build

ARG AFP_URL=https://foss.heptapod.net/isa-afp/afp-devel/-/archive/branch/default/afp-devel-branch-default.tar.gz

RUN apt-get update \
    && DEBIAN_FRONTEND=noninteractive apt-get install -y --no-install-recommends \
       ca-certificates curl libfontconfig1 libgomp1 perl \
       cmake make clang binutils libarchive-dev nlohmann-json3-dev libboost-program-options-dev \
       pkg-config nettle-dev libacl1-dev liblzma-dev libzstd-dev liblz4-dev libbz2-dev zlib1g-dev \
       libxml2-dev libicu-dev \
    && rm -rf /var/lib/apt/lists/*

COPY versions.cmake /tmp/
RUN version=$(sed -n 's/^set(HUMBLE_ISABELLE_VERSION \(.*\))$/\1/p' /tmp/versions.cmake) \
    && mkdir /opt/isabelle \
    && curl -fsSL "https://isabelle.in.tum.de/website-Isabelle$version/dist/Isabelle${version}_linux.tar.gz" \
       | tar -xz -C /opt/isabelle --strip-components=1 \
    && ln -s /opt/isabelle/bin/isabelle /usr/local/bin/isabelle

RUN mkdir /opt/afp \
    && curl -fsSL "$AFP_URL" | tar -xz -C /opt/afp --strip-components=1 \
    && isabelle components -u /opt/afp/thys

WORKDIR /humble
COPY . .
RUN cmake -S . -B build -DCMAKE_BUILD_TYPE=Release -DHUMBLE_BUILD_THEORIES=ON -DHUMBLE_STATIC=ON \
    && cmake --build build -j

FROM scratch
COPY --from=build /humble/generated /generated
COPY --from=build /humble/build /build
