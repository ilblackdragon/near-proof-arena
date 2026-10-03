# Delivery container for the arena Firecracker runner. Contains only three
# static binaries; no shell, no libc, no package manager. The security
# boundary is the microVM started inside it, not this container.
FROM scratch
COPY firecracker jailer arena-fc-shim /usr/local/bin/
ENTRYPOINT ["/usr/local/bin/arena-fc-shim"]
