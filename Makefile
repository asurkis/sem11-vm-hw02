all:
	$(MAKE) -C src
	$(MAKE) -C regression

clean:
	$(MAKE) -C src clean
	$(MAKE) -C regression clean
