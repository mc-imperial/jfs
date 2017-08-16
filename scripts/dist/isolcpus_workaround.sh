# HACK: See https://github.com/moby/moby/issues/31086
if [ "X${ISOLCPUS_WORKAROUND}" = "X1" ]; then
  # Use round robin scheduler
  sudo chrt -r -p 1 $$
fi
