package codegen;

import codegen.*;

import java.io.*;
import java.nio.file.Files;
import java.nio.file.Path;

import com.fasterxml.jackson.databind.*;


class Parser {
    public static void main(String[] args) {
        if (args.length != 1) {
            System.out.println("Need json file.");
            return;
        }

        // read file
        String json = null;
        try {
            Path filePath = Path.of(args[0]);
            json = Files.readString(filePath);
        } catch (Exception e) {
            System.out.println("Cannot read file");
        }

        // convert to to JSON
        JsonNode jsonNode = null;
        try {
            ObjectMapper mapper = new ObjectMapper(); 
            jsonNode = mapper.readTree(json);
        } catch (Exception e) {
            System.out.println("Cannot read JSON");
        }
        
        ClassfileMaker cfm = new ClassfileMaker(jsonNode);
    }
}

