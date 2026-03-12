FROM eclipse-temurin:21-jdk

ARG DEBIAN_FRONTEND=noninteractive
ARG CMAKE_VERSION=4.0.0-rc4
ARG BUILD_AMBER=1

RUN apt-get update \
    && apt-get install -y --no-install-recommends \
        bash \
        build-essential \
        ca-certificates \
        clang \
        curl \
        git \
        graphviz \
        libssl-dev \
        libwayland-client0 \
        ninja-build \
        python3 \
        python3-tabulate \
        spirv-cross \
        sudo \
        wget \
    && rm -rf /var/lib/apt/lists/*

RUN curl -fsSL https://sh.rustup.rs | sh -s -- -y
ENV PATH="/root/.cargo/bin:${PATH}"

RUN git config --global http.postBuffer 157286400 \
    && git config --global core.compression 0 \
    && git config --global http.version HTTP/1.1

RUN wget -q "https://github.com/Kitware/CMake/releases/download/v${CMAKE_VERSION}/cmake-${CMAKE_VERSION}.tar.gz" \
    && tar -xzf "cmake-${CMAKE_VERSION}.tar.gz" \
    && cd "cmake-${CMAKE_VERSION}" \
    && ./bootstrap \
    && make -j"$(nproc)" \
    && make install \
    && cd / \
    && rm -rf "cmake-${CMAKE_VERSION}" "cmake-${CMAKE_VERSION}.tar.gz"

RUN git clone https://github.com/pmer/tla-bin.git /tmp/tla-bin \
    && cd /tmp/tla-bin \
    && ./download_or_update_tla.sh \
    && sudo ./install.sh \
    && rm -rf /tmp/tla-bin

WORKDIR /workdir
COPY glslang glslang

RUN cd glslang \
    && ./update_glslang_sources.py \
    && mkdir -p build \
    && cd build \
    && cmake -DCMAKE_BUILD_TYPE=Release -DCMAKE_INSTALL_PREFIX="$(pwd)/install" .. \
    && make -j"$(nproc)" install

RUN git clone https://github.com/KhronosGroup/Vulkan-Headers.git /tmp/Vulkan-Headers \
    && cmake -S /tmp/Vulkan-Headers -B /tmp/Vulkan-Headers/build -DCMAKE_INSTALL_PREFIX=/usr \
    && cmake --build /tmp/Vulkan-Headers/build -j"$(nproc)" \
    && cmake --install /tmp/Vulkan-Headers/build \
    && rm -rf /tmp/Vulkan-Headers

RUN if [ "${BUILD_AMBER}" = "1" ]; then \
      git clone --depth=1 https://github.com/google/amber.git /tmp/amber \
      && cd /tmp/amber \
      && ./tools/git-sync-deps \
      && cmake -S . -B out/Debug -GNinja \
      && cmake --build out/Debug -j"$(nproc)" \
      && rm -rf /tmp/amber; \
    fi

COPY . /workdir
COPY scripts/run_pipeline.sh /usr/local/bin/run_pipeline.sh

RUN chmod +x /usr/local/bin/run_pipeline.sh \
    && CARGO_TARGET_DIR=Homunculus/target cargo build --release --manifest-path=Homunculus/Cargo.toml

ENTRYPOINT ["/usr/local/bin/run_pipeline.sh"]
