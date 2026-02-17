local BinaryLua = {}


function BinaryLua.encode(source)
    return (source:gsub(".", function(c)
        local byte = string.byte(c)
        local bits = ""
        for i = 7, 0, -1 do
            bits = bits .. ((byte >> i) & 1)
        end
        return bits
    end))
end


function BinaryLua.decode(binary)
    local text = binary:gsub("%s+", "") 
    return (text:gsub("%d%d%d%d%d%d%d%d", function(byte)
        return string.char(tonumber(byte, 2))
    end))
end


function BinaryLua.run(binary)
    local src = BinaryLua.decode(binary)
    local f = loadstring(src)
    if f then
        return f()
    else
        warn("Failed to compile binary.")
    end
end

return BinaryLua
