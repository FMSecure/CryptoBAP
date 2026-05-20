// Ghidra headless post-script.
//
// Emits the subset of GNU objdump-style disassembly that HolBA's
// gcc_supportLib.read_disassembly_file_regions parser consumes.

import java.io.FileOutputStream;
import java.io.OutputStreamWriter;
import java.io.PrintWriter;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import ghidra.app.script.GhidraScript;
import ghidra.program.model.address.Address;
import ghidra.program.model.address.AddressSet;
import ghidra.program.model.listing.Function;
import ghidra.program.model.listing.FunctionIterator;
import ghidra.program.model.listing.Instruction;
import ghidra.program.model.listing.InstructionIterator;
import ghidra.program.model.listing.Listing;
import ghidra.program.model.listing.Program;
import ghidra.program.model.mem.Memory;
import ghidra.program.model.mem.MemoryBlock;
import ghidra.program.model.symbol.Symbol;
import ghidra.program.model.symbol.SymbolTable;

public class ExportObjdumpDa extends GhidraScript {
    private String addrText(Address addr) {
        return String.format("%016x", addr.getOffset());
    }

    private String addrText(long offset) {
        return String.format("%016x", offset);
    }

    private String byteText(Instruction inst, String arch) throws Exception {
        byte[] bytes = inst.getBytes();
        List<Integer> raw = new ArrayList<>();
        for (byte value : bytes) {
            raw.add(value & 0xff);
        }

        String lowered = arch.toLowerCase();
        if ((lowered.equals("arm8") || lowered.equals("aarch64")) && raw.size() == 4) {
            List<Integer> reversed = new ArrayList<>();
            for (int index = raw.size() - 1; index >= 0; index--) {
                reversed.add(raw.get(index));
            }
            raw = reversed;
        }
        else if (lowered.equals("m0") || lowered.equals("m0_mod")
                || lowered.equals("arm-m0") || lowered.equals("cortex-m0")) {
            List<Integer> swapped = new ArrayList<>();
            for (int index = 0; index < raw.size(); index += 2) {
                if (index + 1 < raw.size()) {
                    swapped.add(raw.get(index + 1));
                }
                swapped.add(raw.get(index));
            }
            raw = swapped;
        }

        StringBuilder builder = new StringBuilder();
        for (int value : raw) {
            builder.append(String.format("%02x", value));
        }
        return builder.toString();
    }

    private boolean sectionSelected(MemoryBlock block, List<String> selected) {
        return (selected.size() == 1 && selected.get(0).equals("*")) || selected.contains(block.getName());
    }

    private Map<String, String> functionsByEntry(Program program, MemoryBlock block) {
        Map<String, String> entries = new HashMap<>();
        FunctionIterator functions = program.getFunctionManager().getFunctions(true);
        for (Function function : functions) {
            Address entry = function.getEntryPoint();
            if (block.contains(entry)) {
                entries.put(entry.toString(), function.getName());
            }
        }
        return entries;
    }

    private String primarySymbolName(SymbolTable symbolTable, Address address) {
        Symbol symbol = symbolTable.getPrimarySymbol(address);
        return symbol == null ? null : symbol.getName();
    }

    private boolean useSectionRelativeAddresses(Program program) {
        String name = program.getName();
        String path = program.getExecutablePath();
        return name.endsWith(".o") || name.endsWith(".obj")
            || path.endsWith(".o") || path.endsWith(".obj");
    }

    private long displayOffset(Address address, MemoryBlock block, boolean sectionRelative) {
        long offset = address.getOffset();
        if (sectionRelative) {
            return offset - block.getStart().getOffset();
        }
        return offset;
    }

    private String renderInstruction(
            Instruction inst, MemoryBlock block, boolean sectionRelative, SymbolTable symbolTable) {
        String mnemonic = inst.getMnemonicString();
        String lowered = mnemonic.toLowerCase();
        if (!(lowered.equals("b") || lowered.equals("bl"))) {
            return inst.toString();
        }

        Address[] flows = inst.getFlows();
        if (flows.length == 0) {
            return inst.toString();
        }

        Address target = flows[0];
        String label = primarySymbolName(symbolTable, target);
        if (label == null) {
            return inst.toString();
        }

        long targetOffset = block.contains(target)
            ? displayOffset(target, block, sectionRelative)
            : target.getOffset();
        return mnemonic + " " + Long.toHexString(targetOffset) + " <" + label + ">";
    }

    @Override
    protected void run() throws Exception {
        String[] args = getScriptArgs();
        if (args.length < 3) {
            throw new IllegalArgumentException(
                "expected arguments: <output.da> <arch> <comma-separated-sections>");
        }

        String outputPath = args[0];
        String arch = args[1];
        List<String> selectedSections = new ArrayList<>();
        for (String section : args[2].split(",")) {
            String trimmed = section.trim();
            if (!trimmed.isEmpty()) {
                selectedSections.add(trimmed);
            }
        }
        if (selectedSections.isEmpty()) {
            selectedSections.add(".text");
        }

        Program program = currentProgram;
        Listing listing = program.getListing();
        Memory memory = program.getMemory();
        SymbolTable symbolTable = program.getSymbolTable();
        boolean sectionRelative = useSectionRelativeAddresses(program);

        try (PrintWriter handle = new PrintWriter(
                new OutputStreamWriter(new FileOutputStream(outputPath), StandardCharsets.UTF_8))) {
            handle.printf("%n%s:     file format %s%n%n%n", program.getName(), program.getLanguageID());
            for (MemoryBlock block : memory.getBlocks()) {
                if (!block.isExecute() || !sectionSelected(block, selectedSections)) {
                    continue;
                }
                handle.printf("Disassembly of section %s:%n%n", block.getName());
                Map<String, String> entries = functionsByEntry(program, block);
                InstructionIterator instructions =
                    listing.getInstructions(new AddressSet(block.getStart(), block.getEnd()), true);
                boolean wroteLabel = false;
                for (Instruction inst : instructions) {
                    Address address = inst.getAddress();
                    long offset = displayOffset(address, block, sectionRelative);
                    String key = address.toString();
                    String label = entries.get(key);
                    if (label == null) {
                        label = primarySymbolName(symbolTable, address);
                    }
                    if (label != null) {
                        handle.printf("%s <%s>:%n", addrText(offset), label);
                        wroteLabel = true;
                    }
                    else if (!wroteLabel) {
                        handle.printf("%s <%s>:%n", addrText(offset), block.getName());
                        wroteLabel = true;
                    }
                    handle.printf("  %4x:\t%-10s\t%s%n",
                        offset, byteText(inst, arch),
                        renderInstruction(inst, block, sectionRelative, symbolTable));
                }
                handle.println();
            }
        }
    }
}
