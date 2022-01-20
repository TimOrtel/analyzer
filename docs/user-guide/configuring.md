# Configuring

## JSON conf files

### JSON schema

#### VSCode
In `.vscode/settings.json` add the following:
```json
{
    "json.schemas": [
        {
            "fileMatch": [
                "/conf/*.json",
                "/tests/incremental/*/*.json"
            ],
            "url": "/src/util/options.schema.json"
        }
    ]
}
```