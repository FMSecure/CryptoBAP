# Ghidra headless post-script.
#
# Emits the subset of GNU objdump-style disassembly that HolBA's
# gcc_supportLib.read_disassembly_file_regions parser consumes.

from ghidra.program.model.address import AddressSet


def _addr_text(addr):
    return ("%x" % addr.getOffset()).rjust(16, "0")


def _byte_text(inst, arch):
    raw = [b & 0xFF for b in inst.getBytes()]
    lowered = arch.lower()
    if lowered in ("arm8", "aarch64") and len(raw) == 4:
        raw = list(reversed(raw))
    elif lowered in ("m0", "m0_mod", "arm-m0", "cortex-m0"):
        pairs = [raw[index : index + 2] for index in range(0, len(raw), 2)]
        raw = [byte for pair in pairs for byte in reversed(pair)]
    return "".join("%02x" % byte for byte in raw)


def _section_selected(block, selected):
    return selected == ["*"] or block.getName() in selected


def _functions_by_entry(function_manager, block):
    entries = {}
    functions = function_manager.getFunctions(True)
    for function in functions:
        entry = function.getEntryPoint()
        if block.contains(entry):
            entries[entry.toString()] = function.getName()
    return entries


def _primary_symbol_name(symbol_table, address):
    symbol = symbol_table.getPrimarySymbol(address)
    if symbol is None:
        return None
    return symbol.getName()


args = getScriptArgs()
if len(args) < 3:
    raise ValueError("expected arguments: <output.da> <arch> <comma-separated-sections>")

output_path = args[0]
arch = args[1]
selected_sections = [section.strip() for section in args[2].split(",") if section.strip()]
if not selected_sections:
    selected_sections = [".text"]

program = currentProgram
listing = program.getListing()
memory = program.getMemory()
function_manager = program.getFunctionManager()
symbol_table = program.getSymbolTable()

with open(output_path, "w") as handle:
    handle.write("\n%s:     file format %s\n\n\n" % (program.getName(), program.getLanguageID()))
    for block in memory.getBlocks():
        if not block.isExecute() or not _section_selected(block, selected_sections):
            continue
        handle.write("Disassembly of section %s:\n\n" % block.getName())
        entries = _functions_by_entry(function_manager, block)
        instructions = listing.getInstructions(AddressSet(block.getStart(), block.getEnd()), True)
        wrote_label = False
        for inst in instructions:
            address = inst.getAddress()
            key = address.toString()
            label = entries.get(key)
            if label is None:
                label = _primary_symbol_name(symbol_table, address)
            if label is not None:
                handle.write("%s <%s>:\n" % (_addr_text(address), label))
                wrote_label = True
            elif not wrote_label:
                handle.write("%s <%s>:\n" % (_addr_text(address), block.getName()))
                wrote_label = True
            handle.write(
                "  %s:\t%-10s\t%s\n" % (
                    ("%x" % address.getOffset()).rjust(4, " "),
                    _byte_text(inst, arch),
                    inst.toString(),
                )
            )
        handle.write("\n")
