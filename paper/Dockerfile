FROM debian:bookworm-slim

# Match the existing manuscript builder and verify the upstream Linux binary.
RUN apt-get update \
    && apt-get install -y --no-install-recommends ca-certificates curl python3 poppler-utils \
    && rm -rf /var/lib/apt/lists/* \
    && curl --fail --location --retry 3 \
       https://github.com/tectonic-typesetting/tectonic/releases/download/tectonic%400.15.0/tectonic-0.15.0-x86_64-unknown-linux-musl.tar.gz \
       --output /tmp/tectonic.tar.gz \
    && echo "dfb82876f2986862996e564fa507a9e576e0c1e3bee63c2c1bd677c2543e6407  /tmp/tectonic.tar.gz" | sha256sum --check - \
    && tar -xzf /tmp/tectonic.tar.gz -C /usr/local/bin tectonic \
    && rm /tmp/tectonic.tar.gz \
    && tectonic --version

WORKDIR /work
ENV HOME=/tmp
CMD ["python3", "scripts/build_paper.py"]
