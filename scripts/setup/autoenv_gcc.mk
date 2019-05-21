# we need to have a HOLBA_DIR for this one
ifndef HOLBA_DIR

      $(info !!! WARNING)
      $(info !!! - HOLBA_DIR undefined, cannot find autoenv_base.mk)
  
else

  HOLBA_AUTOENV_BASE_MK = $(HOLBA_DIR)/scripts/setup/autoenv_base.mk
  ifeq ("$(wildcard $(HOLBA_AUTOENV_BASE_MK))", "")
    $(info !!! ERROR)
    $(error $(HOLBA_AUTOENV_BASE_MK) does not exist)
  endif

  include $(HOLBA_AUTOENV_BASE_MK)

  # use env.sh in HOLBA_OPT_DIR, if found
  ifdef HOLBA_OPT_DIR
    HOLBA_ENV_SH = $(HOLBA_OPT_DIR)/env.sh
    ifneq ("$(wildcard $(HOLBA_ENV_SH))", "")
      $(info !!! including $(HOLBA_ENV_SH))
      include $(HOLBA_ENV_SH)
    else
      $(info !!! WARNING)
      $(info !!! - $(HOLBA_ENV_SH) not found, you may run install_mk_env.sh)
    endif
    $(info )
  endif

  # fail if gcc variable is still undefined
  ifndef HOLBA_GCC_ARM8_CROSS
    $(info !!! ERROR)
    $(error HOLBA_GCC_ARM8_CROSS undefined)
  endif

  $(info !!! Using HOLBA_GCC_ARM8_CROSS=$(HOLBA_GCC_ARM8_CROSS))

endif

$(info )

