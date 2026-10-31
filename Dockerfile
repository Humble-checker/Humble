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

FROM scratch AS export
COPY --from=build /humble/generated /generated
# Only the binary: the rest of the build tree, CMakeCache.txt included, is tied to /humble/build
# and would make a local `cmake -B build` refuse to run.
COPY --from=build /humble/build/humble /build/humble

# The default stage: a shell with humble on PATH, started in /shared, where the host's shared/
# folder is mounted for models and results. humble is static, so the image needs nothing else.
FROM ubuntu:26.04
COPY --from=build /humble/build/humble /usr/local/bin/humble
WORKDIR /shared
CMD ["bash"]
