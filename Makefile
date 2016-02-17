LOCAL_MAKEFILE="Makefile.coq"
TLC_DIR="tlc/src"


.PHONY: all
all: local

.PHONY: tlc
tlc:
	$(MAKE) -C $(TLC_DIR)

.PHONY: local
local: tlc
	$(MAKE) -f $(LOCAL_MAKEFILE)

.PHONY: clean
clean:
	$(MAKE) -f $(LOCAL_MAKEFILE) clean

.PHONY: mrproper
mrproper: clean
	$(MAKE) -C $(TLC_DIR) clean
